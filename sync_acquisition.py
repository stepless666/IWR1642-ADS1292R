import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import serial
import threading
import time
import struct
import csv
import os
from collections import deque
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import numpy as np
import subprocess
from scipy import signal

class SyncAcquisition:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("同步采集系统")
        self.root.geometry("1800x1200")
        
        # 数据缓冲区
        self.window_size = 10 * 128
        self.ch1_data = deque([0] * self.window_size, maxlen=self.window_size)
        self.ch2_data = deque([0] * self.window_size, maxlen=self.window_size)
        self.cv1_data = deque([0] * self.window_size, maxlen=self.window_size)
        self.cv2_data = deque([0] * self.window_size, maxlen=self.window_size)
        
        # 计算值
        self.computed_val1 = 0
        self.computed_val2 = 0
        
        # 串口相关
        self.ads_serial_port = None  # ADS1292串口
        self.iwr_serial_port = None  # IWR1642串口
        self.is_running = False
        self.logging = False
        self.log_file = None
        self.log_writer = None
        
        # 包解析状态机 (ADS1292)
        self.pc_rx_state = 0
        self.CESState_Init = 0
        self.CESState_SOF1_Found = 1
        self.CESState_SOF2_Found = 2
        self.CESState_PktLen_Found = 3
        
        # 包常量
        self.CES_CMDIF_PKT_START_1 = 0x0A
        self.CES_CMDIF_PKT_START_2 = 0xFA
        self.CES_CMDIF_PKT_STOP = 0x0B
        self.CES_CMDIF_IND_LEN = 2
        self.CES_CMDIF_IND_LEN_MSB = 3
        self.CES_CMDIF_IND_PKTTYPE = 4
        self.CES_CMDIF_PKT_OVERHEAD = 5
        
        # 包解析变量
        self.CES_Pkt_Len = 0
        self.CES_Pkt_Pos_Counter = 0
        self.CES_Data_Counter = 0
        self.CES_Pkt_PktType = 0
        self.CES_Pkt_Data_Counter = []
        
        # 脚本路径
        self.script_dir = os.path.dirname(os.path.abspath(__file__))
        
        # GUI更新定时器
        self.plot_update_timer = None
        self.plot_update_interval = 50  # 50ms更新一次图形
        
        # 信号处理相关
        self.fs = 128  # 采样频率，根据实际情况调整
        self.init_filters()
        
        # DCA1000配置
        self.dca1000_cmd_dir = os.path.join(self.script_dir, 'mmWave_script-master','DCA1000', 'Custom-build', 'Release')
        self.fpga_cmd = 'DCA1000EVM_CLI_Control.exe fpga cf.json'
        
        self.setup_ui()
        self.update_ports()
    
    def init_filters(self):
        """初始化滤波器"""
        # 与Arduino代码保持一致，使用40Hz FIR低通滤波器
        # Arduino库中的161阶FIR滤波器系数
        CoeffBuf_40Hz_LowPass = [-72, 122, -31, -99, 117, 0, -121, 105, 34,
                                  -137, 84, 70, -146, 55, 104, -147, 20, 135,
                                  -137, -21, 160, -117, -64, 177, -87, -108, 185,
                                  -48, -151, 181, 0, -188, 164, 54, -218, 134,
                                  112, -238, 90, 171, -244, 33, 229, -235, -36,
                                  280, -208, -115, 322, -161, -203, 350, -92, -296,
                                  361, 0, -391, 348, 117, -486, 305, 264, -577,
                                  225, 445, -660, 93, 676, -733, -119, 991, -793,
                                  -480, 1486, -837, -1226, 2561, -865, -4018, 9438, 20972,
                                  9438, -4018, -865, 2561, -1226, -837, 1486, -480, -793,
                                  991, -119, -733, 676, 93, -660, 445, 225, -577,
                                  264, 305, -486, 117, 348, -391, 0, 361, -296,
                                  -92, 350, -203, -161, 322, -115, -208, 280, -36,
                                  -235, 229, 33, -244, 171, 90, -238, 112, 134,
                                  -218, 54, 164, -188, 0, 181, -151, -48, 185,
                                  -108, -87, 177, -64, -117, 160, -21, -137, 135,
                                  20, -147, 104, 55, -146, 70, 84, -137, 34,
                                  105, -121, 0, 117, -99, -31, 122, -72]
        
        # 归一化系数
        self.ecg_fir_b = np.array(CoeffBuf_40Hz_LowPass, dtype=np.float64) / 32768.0
        self.ecg_fir_buffer = np.zeros(len(self.ecg_fir_b))
        self.ecg_fir_ptr = 0
        
        # 初始化FIR滤波器状态
        self.ecg_fir_zi = np.zeros(max(len(self.ecg_fir_b) - 1, 1))
        
        # 毛刺抑制缓冲区
        self.ecg_spike_buffer = []
        self.ecg_spike_buffer_size = 3  # 轻度平滑的缓冲区大小
        
        # 基线漂移去除缓冲区
        self.ecg_baseline_buffer = []
        self.ecg_baseline_buffer_size = 100  # 基线计算的缓冲区大小
        
        # 设计50Hz陷波滤波器，去除工频干扰
        notch_freq = 50.0  # 工频频率
        quality_factor = 30.0  # 陷波滤波器品质因数
        self.notch_b, self.notch_a = signal.iirnotch(notch_freq, quality_factor, self.fs)
        
        # 初始化陷波滤波器状态
        self.notch_zi = signal.lfilter_zi(self.notch_b, self.notch_a) * 0
        
        # 设计呼吸信号的低通滤波器
        # 呼吸信号频率通常在 0.1-0.5 Hz 之间
        nyquist = 0.5 * self.fs
        order = 4
        resp_cutoff = 0.6  # 呼吸信号截止频率
        resp_low = resp_cutoff / nyquist
        
        # 设计巴特沃斯低通滤波器
        self.resp_b, self.resp_a = signal.butter(order, resp_low, btype='low')
        
        # 初始化呼吸滤波器状态
        self.resp_zi = signal.lfilter_zi(self.resp_b, self.resp_a) * 0
    
    def filter_ecg(self, ecg_signal):
        """对ECG信号进行滤波处理
        
        Args:
            ecg_signal: 原始ECG信号
            
        Returns:
            滤波后的ECG信号
        """
        # 应用与Arduino库相同的161阶FIR滤波器
        self.ecg_fir_buffer[self.ecg_fir_ptr] = ecg_signal
        self.ecg_fir_ptr = (self.ecg_fir_ptr + 1) % len(self.ecg_fir_b)
        
        # 计算FIR滤波输出
        acc = 0
        ptr = self.ecg_fir_ptr
        for k in range(len(self.ecg_fir_b)):
            acc += self.ecg_fir_b[k] * self.ecg_fir_buffer[(ptr - 1 - k + len(self.ecg_fir_b)) % len(self.ecg_fir_b)]
        
        # 饱和处理
        if acc > 32767:
            acc = 32767
        elif acc < -32768:
            acc = -32768
        
        fir_output = int(acc)
        
        # 基线漂移去除 - 移动平均法
        self.ecg_baseline_buffer.append(fir_output)
        if len(self.ecg_baseline_buffer) > self.ecg_baseline_buffer_size:
            self.ecg_baseline_buffer.pop(0)
        
        # 计算基线
        if len(self.ecg_baseline_buffer) > 0:
            baseline = sum(self.ecg_baseline_buffer) / len(self.ecg_baseline_buffer)
        else:
            baseline = 0
        
        # 去除基线漂移
        baseline_corrected = fir_output - baseline
        
        # 应用陷波滤波器去除工频干扰
        notch_filtered, self.notch_zi = signal.lfilter(self.notch_b, self.notch_a, [baseline_corrected], zi=self.notch_zi)
        
        # 添加到毛刺抑制缓冲区
        self.ecg_spike_buffer.append(notch_filtered[0])
        if len(self.ecg_spike_buffer) > self.ecg_spike_buffer_size:
            self.ecg_spike_buffer.pop(0)
        
        # 使用轻度移动平均抑制毛刺
        if len(self.ecg_spike_buffer) >= self.ecg_spike_buffer_size:
            # 对连续的样本取平均，轻度平滑
            smoothed = sum(self.ecg_spike_buffer) / len(self.ecg_spike_buffer)
        else:
            smoothed = notch_filtered[0]
        
        return smoothed
    
    def filter_resp(self, resp_signal):
        """对呼吸信号进行滤波处理
        
        Args:
            resp_signal: 原始呼吸信号
            
        Returns:
            滤波后的呼吸信号
        """
        # 应用低通滤波器
        filtered_signal, self.resp_zi = signal.lfilter(self.resp_b, self.resp_a, [resp_signal], zi=self.resp_zi)
        return filtered_signal[0]
        
    def setup_ui(self):
        # 主框架
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # 控制面板 - 分为两个设备的配置
        control_frame = ttk.Frame(main_frame)
        control_frame.pack(fill=tk.X, pady=(0, 10))
        
        # ADS1292配置面板
        ads_frame = ttk.LabelFrame(control_frame, text="ADS1292配置")

        ads_frame.grid(row=0, column=0, padx=(0, 20), pady=5, sticky=tk.W)
        
        # ADS1292端口选择
        ttk.Label(ads_frame, text="端口:").grid(row=0, column=0, padx=(0, 5), pady=5)
        self.ads_port_var = tk.StringVar()
        self.ads_port_combo = ttk.Combobox(ads_frame, textvariable=self.ads_port_var, width=15)
        self.ads_port_combo.grid(row=0, column=1, padx=(0, 10), pady=5)
        
        # ADS1292设备选择
        ttk.Label(ads_frame, text="设备:").grid(row=0, column=2, padx=(0, 5), pady=5)
        self.ads_device_var = tk.StringVar(value="ADS1292R")
        ads_device_combo = ttk.Combobox(
            ads_frame,
            textvariable=self.ads_device_var,
            values=["ADS1292R", "ADS1293", "AFE4490", "MAX86150", "Pulse Express", "MAX30003"],
            width=15
        )
        ads_device_combo.grid(row=0, column=3, padx=(0, 10), pady=5)
        
        # IWR1642配置面板
        iwr_frame = ttk.LabelFrame(control_frame, text="IWR1642配置")
        iwr_frame.grid(row=0, column=1, padx=(0, 20), pady=5, sticky=tk.W)
        
        # IWR1642端口选择
        ttk.Label(iwr_frame, text="端口:").grid(row=0, column=0, padx=(0, 5), pady=5)
        self.iwr_port_var = tk.StringVar(value="COM3")
        self.iwr_port_combo = ttk.Combobox(iwr_frame, textvariable=self.iwr_port_var, width=15)
        self.iwr_port_combo.grid(row=0, column=1, padx=(0, 10), pady=5)
        
        # 配置文件选择
        ttk.Label(iwr_frame, text="配置文件:").grid(row=0, column=2, padx=(0, 5), pady=5)
        self.cfg_file_var = tk.StringVar()
        self.cfg_file_entry = ttk.Entry(iwr_frame, textvariable=self.cfg_file_var, width=30)
        self.cfg_file_entry.grid(row=0, column=3, padx=(0, 5), pady=5)
        self.browse_btn = ttk.Button(iwr_frame, text="浏览", command=self.browse_cfg_file)
        self.browse_btn.grid(row=0, column=4, pady=5)
        
        # 默认配置文件路径
        self.default_cfg_path = os.path.join(self.script_dir, 'mmWave_script-master', 'Python4IWR', 'cfg', 'test1cfg.cfg')
        self.cfg_file_var.set(self.default_cfg_path)
        
        # 数据保存目录
        save_frame = ttk.LabelFrame(control_frame, text="ADS1292数据保存")
        save_frame.grid(row=0, column=2, padx=(0, 20), pady=5, sticky=tk.W)
        
        ttk.Label(save_frame, text="ADS1292数据保存目录:").grid(row=0, column=0, padx=(0, 5), pady=5)
        self.save_path_var = tk.StringVar(value=os.path.join(self.script_dir, "data"))
        self.save_path_entry = ttk.Entry(save_frame, textvariable=self.save_path_var, width=30)
        self.save_path_entry.grid(row=0, column=1, padx=(0, 5), pady=5)
        self.browse_save_btn = ttk.Button(save_frame, text="浏览", command=self.browse_save_path)
        self.browse_save_btn.grid(row=0, column=2, pady=5)
        
        ttk.Label(save_frame, text="文件名:").grid(row=1, column=0, padx=(0, 5), pady=5)
        self.filename_var = tk.StringVar(value="acquisition_data")
        self.filename_entry = ttk.Entry(save_frame, textvariable=self.filename_var, width=30)
        self.filename_entry.grid(row=1, column=1, padx=(0, 5), pady=5)
        
        # 主控制按钮
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(fill=tk.X, pady=(0, 10))
        
        # 开始/停止同步采集按钮
        self.start_button = ttk.Button(
            button_frame, 
            text="开始同步采集", 
            command=self.toggle_sync_acquisition,
            style="Accent.TButton"
        )
        self.start_button.pack(side=tk.LEFT, padx=(0, 10))
        
        # 刷新端口按钮
        refresh_button = ttk.Button(
            button_frame, 
            text="刷新端口", 
            command=self.update_ports
        )
        refresh_button.pack(side=tk.LEFT)
        
        # 计算值显示
        self.val1_label = ttk.Label(button_frame, text="RR: -- bpm", font=('Arial', 12))
        self.val1_label.pack(side=tk.LEFT, padx=(20, 20))
        
        self.val2_label = ttk.Label(button_frame, text="HR: -- bpm", font=('Arial', 12))
        self.val2_label.pack(side=tk.LEFT, padx=(20, 20))
        
        # 图形显示区域
        graph_frame = ttk.Frame(main_frame)
        graph_frame.pack(fill=tk.BOTH, expand=True)
        
        # 创建matplotlib图形
        self.fig, (self.ax1, self.ax2, self.ax3) = plt.subplots(3, 1, figsize=(12, 8))
        
        # ECG通道
        self.line1, = self.ax1.plot([], [], 'g-', linewidth=1.5)
        self.ax1.set_title('ECG Channel 1')
        self.ax1.set_ylabel('Amplitude')
        self.ax1.grid(True)
        
        # PPG通道
        self.line2, = self.ax2.plot([], [], 'y-', linewidth=1.5)
        self.ax2.set_title('Channel 2')
        self.ax2.set_ylabel('Amplitude')
        self.ax2.grid(True)
        
        # 计算值
        self.line3, = self.ax3.plot([], [], 'b-', linewidth=1.5)
        self.ax3.set_title('Computed Values')
        self.ax3.set_ylabel('Value')
        self.ax3.set_xlabel('Time')
        self.ax3.grid(True)
        
        # 将图形嵌入tkinter
        self.canvas = FigureCanvasTkAgg(self.fig, master=graph_frame)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # 状态栏
        self.status_var = tk.StringVar(value="就绪")
        status_bar = ttk.Label(main_frame, textvariable=self.status_var, relief=tk.SUNKEN)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # 定义样式
        self.style = ttk.Style()
        self.style.configure("Accent.TButton", foreground="red", font=('Arial', 11, 'bold'))
        
    def browse_cfg_file(self):
        """浏览选择配置文件"""
        filename = filedialog.askopenfilename(
            title="选择配置文件",
            filetypes=[("CFG files", "*.cfg"), ("All files", "*.*")]
        )
        if filename:
            self.cfg_file_var.set(filename)
    
    def browse_save_path(self):
        """浏览选择保存目录"""
        directory = filedialog.askdirectory(title="选择保存目录")
        if directory:
            self.save_path_var.set(directory)
    
    def update_ports(self):
        """更新可用端口列表"""
        import serial.tools.list_ports
        ports = [port.device for port in serial.tools.list_ports.comports()]
        
        # 更新ADS1292端口列表
        self.ads_port_combo['values'] = ports
        if ports and not self.ads_port_var.get() in ports:
            self.ads_port_var.set(ports[0])
        
        # 更新IWR1642端口列表
        self.iwr_port_combo['values'] = ports
        if ports and not self.iwr_port_var.get() in ports:
            self.iwr_port_var.set(ports[1] if len(ports) > 1 else ports[0])
    
    def toggle_sync_acquisition(self):
        """切换同步采集状态"""
        if not self.is_running:
            self.start_sync_acquisition()
        else:
            self.stop_sync_acquisition()
    
    def start_sync_acquisition(self):
        """开始同步采集"""
        try:
            # 1. 准备保存目录
            save_path = self.save_path_var.get()
            if not os.path.exists(save_path):
                os.makedirs(save_path)
            
            # 2. 启动ADS1292数据记录
            self.start_auto_logging()
            
            # 3. 打开ADS1292串口
            self.open_ads_serial()
            
            # 4. 配置DCA1000和IWR1642（不发送sensorStart）
            self.configure_iwr1642(skip_sensor_start=True)
            
            # 5. 设置运行状态
            self.is_running = True
            
            # 6. 启动数据读取线程
            self.read_thread = threading.Thread(target=self.read_serial_data, daemon=True)
            self.read_thread.start()
            
            # 7. 发送sensorStart命令，同时开始采集
            if self.iwr_serial_port:
                self.iwr_serial_port.write(('sensorStart\n').encode())
                print('>>> sensorStart')
                time.sleep(0.01)
            
            # 8. 启动绘图更新定时器
            self.start_plot_updates()
            self.start_button.config(text="停止同步采集")
            self.status_var.set("正在进行同步采集...")
            
        except Exception as e:
            messagebox.showerror("错误", f"启动同步采集失败: {str(e)}")
            self.stop_sync_acquisition()
    
    def stop_sync_acquisition(self):
        """停止同步采集"""
        self.is_running = False
        
        # 停止IWR1642
        if self.iwr_serial_port:
            self.iwr_serial_port.write(('sensorStop\n').encode())
            self.iwr_serial_port.close()
            self.iwr_serial_port = None
        
        # 停止ADS1292
        if self.ads_serial_port:
            self.ads_serial_port.close()
            self.ads_serial_port = None
        
        # 停止数据记录
        self.stop_logging()
        
        # 停止绘图更新
        self.stop_plot_updates()
        
        self.start_button.config(text="开始同步采集")
        self.status_var.set("已停止同步采集")
    
    def configure_iwr1642(self, skip_sensor_start=False):
        """配置IWR1642雷达
        
        Args:
            skip_sensor_start (bool): 是否跳过发送sensorStart命令
        """
        try:
            # 检查DCA1000命令目录是否存在
            if not os.path.exists(self.dca1000_cmd_dir):
                raise Exception(f"DCA1000命令目录不存在: {self.dca1000_cmd_dir}")
            
            # 检查DCA1000 CLI工具是否存在
            fpga_tool_path = os.path.join(self.dca1000_cmd_dir, 'DCA1000EVM_CLI_Control.exe')
            record_tool_path = os.path.join(self.dca1000_cmd_dir, 'DCA1000EVM_CLI_Record.exe')
            cf_json_path = os.path.join(self.dca1000_cmd_dir, 'cf.json')
            
            if not os.path.exists(fpga_tool_path):
                raise Exception(f"DCA1000EVM_CLI_Control.exe不存在: {fpga_tool_path}")
            if not os.path.exists(record_tool_path):
                raise Exception(f"DCA1000EVM_CLI_Record.exe不存在: {record_tool_path}")
            if not os.path.exists(cf_json_path):
                raise Exception(f"cf.json配置文件不存在: {cf_json_path}")
            
            # 执行DCA1000 FPGA配置
            fpga_result = subprocess.run(
                self.fpga_cmd, 
                shell=True, 
                capture_output=True, 
                text=True, 
                cwd=self.dca1000_cmd_dir
            )
            if fpga_result.returncode != 0:
                raise Exception(f"DCA1000 FPGA配置失败: {fpga_result.stderr}")
            
            # 启动数据记录
            #timestamp = time.strftime("%Y%m%d_%H%M%S")
            filename = self.filename_var.get()
            record_filename = f"{filename}_IWR1642"
            record_command = f'DCA1000EVM_CLI_Record.exe start_record cf.json {record_filename}'
            
            # 使用Popen异步执行，避免阻塞主线程
            self.record_process = subprocess.Popen(
                record_command, 
                shell=True, 
                text=True, 
                cwd=self.dca1000_cmd_dir
            )
            
            # 检查配置文件是否存在
            file_cfg = self.cfg_file_var.get()
            if not os.path.exists(file_cfg):
                raise Exception(f"IWR1642配置文件不存在: {file_cfg}")
            
            # 读取配置文件
            with open(file_cfg, 'r') as f:
                config = [line.rstrip('\r\n') for line in f]
            
            # 打开IWR1642串口
            serial_port_CLI = self.iwr_port_var.get()
            if not serial_port_CLI:
                raise Exception("未指定IWR1642串口")
            
            print(f'Sending {file_cfg} to IWR1642 on {serial_port_CLI}')
            
            # 配置IWR1642
            self.iwr_serial_port = serial.Serial(serial_port_CLI, 115200, timeout=1)
            
            # 发送配置命令
            for i in config:
                if i == '':
                    continue
                if i[0] == '%':
                    continue
                if i == 'sensorStart':
                    # 根据参数决定是否发送sensorStart命令
                    if not skip_sensor_start:
                        self.iwr_serial_port.write((i + '\n').encode())
                        print('>>> ' + i)
                        time.sleep(0.01)
                        while self.iwr_serial_port.in_waiting > 0:
                            response = self.iwr_serial_port.readline().decode().strip()
                            if response:
                                print(f'<<< {response}') # 这里会打印出 'Done' 或者 'Error -203' 等
                                if "Error" in response:
                                    messagebox.showerror("配置错误", f"指令 [{i}] 执行失败: {response}")
                                    break
                    continue
                self.iwr_serial_port.write((i + '\n').encode())
                print('>>> ' + i)
                time.sleep(0.01)
            
        except FileNotFoundError as e:
            raise Exception(f"文件不存在错误: {str(e)}")
        except serial.SerialException as e:
            raise Exception(f"串口错误: {str(e)}")
        except subprocess.SubprocessError as e:
            raise Exception(f"子进程执行错误: {str(e)}")
        except Exception as e:
            raise Exception(f"配置IWR1642失败: {str(e)}")
    
    def open_ads_serial(self):
        """打开ADS1292串口"""
        try:
            port_name = self.ads_port_var.get()
            if not port_name:
                raise Exception("请选择ADS1292端口")
            
            # 检查端口是否有效
            import serial.tools.list_ports
            available_ports = [port.device for port in serial.tools.list_ports.comports()]
            if port_name not in available_ports:
                raise Exception(f"选择的端口{port_name}不可用，可用端口: {', '.join(available_ports)}")
            
            # 尝试打开串口
            try:
                self.ads_serial_port = serial.Serial(port_name, 57600, timeout=1)
                if not self.ads_serial_port.is_open:
                    raise Exception(f"无法打开ADS1292端口: {port_name}")
            except serial.SerialException as e:
                raise Exception(f"串口通信错误: {str(e)}")
            
        except serial.SerialException as e:
            raise Exception(f"串口错误: {str(e)}")
        except Exception as e:
            raise Exception(f"无法打开ADS1292端口: {str(e)}")
    
    def start_auto_logging(self):
        """开始自动数据记录"""
        try:
            save_path = self.save_path_var.get()
            if not save_path:
                raise Exception("请选择保存目录")
            
            filename = self.filename_var.get()
            if not filename:
                raise Exception("请输入文件名")
            
            # 确保保存目录存在
            if not os.path.exists(save_path):
                try:
                    os.makedirs(save_path)
                except OSError as e:
                    raise Exception(f"无法创建保存目录: {str(e)}")
            
            # 检查目录是否可写
            if not os.access(save_path, os.W_OK):
                raise Exception(f"保存目录不可写: {save_path}")
            
            # 创建日志文件
            #timestamp = time.strftime("%Y%m%d_%H%M%S")
            log_filename = f"{filename}_ADS1292.csv"
            log_path = os.path.join(save_path, log_filename)
            
            try:
                self.log_file = open(log_path, 'w', newline='')
                self.log_writer = csv.writer(self.log_file)
                self.log_writer.writerow(['Timestamp', 'CH1', 'CH2', 'CV1', 'CV2', 'Computed Values'])
                self.log_file.flush()  # 确保头部写入文件
                self.logging = True
                
                print(f"开始记录数据到: {log_path}")
            except IOError as e:
                raise Exception(f"无法创建日志文件: {str(e)}")
            
        except IOError as e:
            raise Exception(f"IO错误: {str(e)}")
        except OSError as e:
            raise Exception(f"系统错误: {str(e)}")
        except Exception as e:
            raise Exception(f"无法创建日志文件: {str(e)}")
    
    def stop_logging(self):
        """停止数据记录"""
        self.logging = False
        if self.log_file:
            self.log_file.close()
            self.log_file = None
            self.log_writer = None
    
    def read_serial_data(self):
        """读取串口数据的线程函数"""
        print("开始读取ADS1292串口数据...")
        packet_count = 0
        byte_count = 0
        
        while self.is_running:
            try:
                if self.ads_serial_port and self.ads_serial_port.in_waiting > 0:
                    # 批量读取数据，减少函数调用次数
                    bytes_available = self.ads_serial_port.in_waiting
                    data = self.ads_serial_port.read(min(bytes_available, 1024))  # 最多读取1024字节
                    byte_count += len(data)
                    
                    # 打印接收到的数据
                    if byte_count % 100 == 0:
                        print(f"已接收 {byte_count} 字节数据")
                    
                    for byte in data:
                        self.pc_process_data(byte)
                time.sleep(0.001)  # 小延迟避免CPU占用过高
            except Exception as e:
                print(f"串口读取错误: {str(e)}")
                break
        
        print(f"停止读取ADS1292串口数据，共接收 {byte_count} 字节")
    
    def pc_process_data(self, rxch):
        """处理接收的数据"""
        # 使用局部变量减少属性查找
        state = self.pc_rx_state
        SOF1 = self.CES_CMDIF_PKT_START_1
        SOF2 = self.CES_CMDIF_PKT_START_2
        STOP = self.CES_CMDIF_PKT_STOP
        IND_LEN = self.CES_CMDIF_IND_LEN
        IND_LEN_MSB = self.CES_CMDIF_IND_LEN_MSB
        IND_PKTTYPE = self.CES_CMDIF_IND_PKTTYPE
        PKT_OVERHEAD = self.CES_CMDIF_PKT_OVERHEAD
        
        # 状态转换和数据处理
        if state == self.CESState_Init:
            if rxch == SOF1:
                # 找到第一个起始字节
                self.pc_rx_state = self.CESState_SOF1_Found
                print(f"找到SOF1: 0x{rxch:02X}")
            elif rxch == 0x0A or rxch == 0xFA or rxch == 0x0B:
                # 打印特殊字节，帮助调试
                print(f"特殊字节: 0x{rxch:02X}")
        elif state == self.CESState_SOF1_Found:
            if rxch == SOF2:
                # 找到第二个起始字节
                self.pc_rx_state = self.CESState_SOF2_Found
                print(f"找到SOF2: 0x{rxch:02X}")
            else:
                # 不是第二个起始字节，重置状态
                self.pc_rx_state = self.CESState_Init
                print(f"不是SOF2: 0x{rxch:02X}, 重置状态")
        elif state == self.CESState_SOF2_Found:
            # 找到数据包长度
            self.pc_rx_state = self.CESState_PktLen_Found
            self.CES_Pkt_Len = rxch
            self.CES_Pkt_Pos_Counter = IND_LEN
            self.CES_Pkt_Data_Counter = []
            print(f"找到数据包长度: 0x{rxch:02X} ({rxch}字节)")
        elif state == self.CESState_PktLen_Found:
            pos_counter = self.CES_Pkt_Pos_Counter + 1
            self.CES_Pkt_Pos_Counter = pos_counter
            
            if pos_counter < PKT_OVERHEAD:
                if pos_counter == IND_LEN_MSB:
                    # 找到长度的高位字节
                    self.CES_Pkt_Len = (rxch << 8) | self.CES_Pkt_Len
                    print(f"找到长度高位: 0x{rxch:02X}, 总长度: {self.CES_Pkt_Len}字节")
                elif pos_counter == IND_PKTTYPE:
                    # 找到数据包类型
                    self.CES_Pkt_PktType = rxch
                    print(f"找到数据包类型: 0x{rxch:02X}")
            elif pos_counter >= PKT_OVERHEAD and pos_counter <= PKT_OVERHEAD + self.CES_Pkt_Len:
                # 读取数据
                if self.CES_Pkt_PktType == 2:
                    self.CES_Pkt_Data_Counter.append(rxch)
                    if len(self.CES_Pkt_Data_Counter) % 4 == 0:
                        print(f"已读取 {len(self.CES_Pkt_Data_Counter)} 字节数据")
                else:
                    print(f"数据包类型不是2: 0x{self.CES_Pkt_PktType:02X}")
            else:
                # 所有数据接收完毕
                if rxch == STOP:
                    # 找到停止字节，处理数据包
                    print(f"找到STOP: 0x{rxch:02X}, 数据包长度: {len(self.CES_Pkt_Data_Counter)}字节")
                    self.process_packet()
                else:
                    print(f"不是STOP: 0x{rxch:02X}, 数据包长度: {len(self.CES_Pkt_Data_Counter)}字节")
                    # 即使没有找到停止字节，也要处理数据包
                    if len(self.CES_Pkt_Data_Counter) >= 8:
                        print("即使没有找到停止字节，也要处理数据包")
                        self.process_packet()
                
                # 重置状态
                self.pc_rx_state = self.CESState_Init
                self.CES_Pkt_Data_Counter = []
    
    def process_packet(self):
        """处理完整数据包"""
        selected_board = self.ads_device_var.get().lower()
        
        # 打印数据包处理信息
        print(f"处理数据包: 设备类型={selected_board}, 数据长度={len(self.CES_Pkt_Data_Counter)}字节")
        
        if selected_board == "ads1292r":
            if len(self.CES_Pkt_Data_Counter) >= 8:
                # 解析CH1数据 (2字节)
                ch1_bytes = self.CES_Pkt_Data_Counter[0:2]
                data1 = struct.unpack('<h', bytes(ch1_bytes))[0]  # 有符号16位小端
                
                # 解析CH2数据 (2字节)
                ch2_bytes = self.CES_Pkt_Data_Counter[2:4]
                data2 = struct.unpack('<h', bytes(ch2_bytes))[0]  # 有符号16位小端
                
                # 解析CV1数据 (2字节)
                cv1_bytes = self.CES_Pkt_Data_Counter[4:6]
                self.computed_val1 = struct.unpack('<h', bytes(cv1_bytes))[0]  # 有符号16位小端
                
                # 解析CV2数据 (2字节)
                cv2_bytes = self.CES_Pkt_Data_Counter[6:8]
                self.computed_val2 = struct.unpack('<h', bytes(cv2_bytes))[0]  # 有符号16位小端
                
                # 打印解析结果
                print(f"ADS1292R数据: CH1={data1}, CH2={data2}, RR={self.computed_val1}, HR={self.computed_val2}")
                
                # 更新数据显示
                self.update_display(data1, data2, self.computed_val1, self.computed_val2)
            else:
                print(f"ADS1292R数据长度不足: 实际={len(self.CES_Pkt_Data_Counter)}字节, 所需=8字节")
        
        elif selected_board == "ads1293":
            if len(self.CES_Pkt_Data_Counter) >= 12:
                # 解析CH1数据 (4字节)
                ch1_bytes = self.CES_Pkt_Data_Counter[0:4]
                data1 = struct.unpack('<i', bytes(ch1_bytes))[0]  # 有符号32位小端
                
                # 解析CH2数据 (4字节)
                ch2_bytes = self.CES_Pkt_Data_Counter[4:8]
                data2 = struct.unpack('<i', bytes(ch2_bytes))[0]  # 有符号32位小端
                
                # 解析CH3数据 (4字节)
                ch3_bytes = self.CES_Pkt_Data_Counter[8:12]
                data3 = struct.unpack('<i', bytes(ch3_bytes))[0]  # 有符号32位小端
                
                # 更新数据显示
                self.update_display(data1, data2, data3, 0)
        
        elif selected_board == "afe4490":
            if len(self.CES_Pkt_Data_Counter) >= 10:
                # 解析CH1数据 (4字节)
                ch1_bytes = self.CES_Pkt_Data_Counter[0:4]
                data1 = struct.unpack('<i', bytes(ch1_bytes))[0]  # 有符号32位小端
                
                # 解析CH2数据 (4字节)
                ch2_bytes = self.CES_Pkt_Data_Counter[4:8]
                data2 = struct.unpack('<i', bytes(ch2_bytes))[0]  # 有符号32位小端
                
                # 解析计算值
                self.computed_val1 = self.CES_Pkt_Data_Counter[8]
                self.computed_val2 = self.CES_Pkt_Data_Counter[9]
                
                # 更新数据显示
                self.update_display(data1, data2, self.computed_val1, self.computed_val2)
        
        elif selected_board == "max86150":
            if len(self.CES_Pkt_Data_Counter) >= 6:
                # 解析CH1数据 (2字节)
                ch1_bytes = self.CES_Pkt_Data_Counter[0:2]
                data1 = struct.unpack('<H', bytes(ch1_bytes))[0]  # 无符号16位小端
                
                # 解析CH2数据 (2字节)
                ch2_bytes = self.CES_Pkt_Data_Counter[2:4]
                data2 = struct.unpack('<H', bytes(ch2_bytes))[0]  # 无符号16位小端
                
                # 解析CH3数据 (2字节)
                ch3_bytes = self.CES_Pkt_Data_Counter[4:6]
                data3 = struct.unpack('<H', bytes(ch3_bytes))[0]  # 无符号16位小端
                
                # 更新数据显示
                self.update_display(data1, data2, data3, 0)
        
        elif selected_board == "pulse express":
            if len(self.CES_Pkt_Data_Counter) >= 4:
                # 解析CH1数据 (2字节)
                ch1_bytes = self.CES_Pkt_Data_Counter[0:2]
                data1 = struct.unpack('<H', bytes(ch1_bytes))[0]  # 无符号16位小端
                
                # 解析CH2数据 (2字节)
                ch2_bytes = self.CES_Pkt_Data_Counter[2:4]
                data2 = struct.unpack('<H', bytes(ch2_bytes))[0]  # 无符号16位小端
                
                # 更新数据显示
                self.update_display(data1, data2, 0, 0)
        
        elif selected_board == "max30003":
            if len(self.CES_Pkt_Data_Counter) >= 12:
                # 解析CH1数据 (4字节)
                ch1_bytes = self.CES_Pkt_Data_Counter[0:4]
                data1 = struct.unpack('<i', bytes(ch1_bytes))[0]  # 有符号32位小端
                
                # 解析CV1数据 (4字节)
                cv1_bytes = self.CES_Pkt_Data_Counter[4:8]
                self.computed_val1 = struct.unpack('<i', bytes(cv1_bytes))[0]  # 有符号32位小端
                
                # 解析CV2数据 (4字节)
                cv2_bytes = self.CES_Pkt_Data_Counter[8:12]
                self.computed_val2 = struct.unpack('<i', bytes(cv2_bytes))[0]  # 有符号32位小端
                
                # 更新数据显示
                self.update_display(data1, 0, self.computed_val1, self.computed_val2)
    
    def update_display(self, ch1, ch2, cv1, cv2):
        """更新显示数据"""
        # 对ECG信号进行滤波处理，去除体动和呼吸干扰
        filtered_ch1 = self.filter_ecg(ch1)
        
        # 对呼吸信号进行滤波处理，去除高频噪声
        filtered_ch2 = self.filter_resp(ch2)
        
        # 添加新数据到缓冲区
        self.ch1_data.append(filtered_ch1)
        self.ch2_data.append(filtered_ch2)
        self.cv1_data.append(cv1)
        self.cv2_data.append(cv2)
        
        # 更新计算值标签
        if self.ads_device_var.get() == "ADS1292R":
            self.val1_label.config(text=f"RR: {cv1} bpm")
            self.val2_label.config(text=f"HR: {cv2} bpm")
        elif self.ads_device_var.get() == "AFE4490":
            self.val1_label.config(text=f"SpO2: {cv1} %")
            self.val2_label.config(text=f"HR: {cv2} bpm")
        elif self.ads_device_var.get() == "MAX30003":
            self.val1_label.config(text=f"RR Interval: {cv1} ms")
            self.val2_label.config(text=f"HR: {cv2} bpm")
        
        # 记录数据到文件
        if self.logging and self.log_writer:
            # 计算 Computed Values，与图形显示中的计算方式一致
            computed_value = (cv1 + cv2) / 2 if cv1 != 0 or cv2 != 0 else 0
            timestamp = time.strftime("%Y-%m-%d %H:%M:%S")
            self.log_writer.writerow([timestamp, filtered_ch1, filtered_ch2, cv1, cv2, computed_value])
            self.log_file.flush()  # 确保数据写入文件
    
    def start_plot_updates(self):
        """启动绘图更新定时器"""
        if self.plot_update_timer is None:
            self.plot_update_timer = self.root.after(self.plot_update_interval, self.update_plots_loop)
    
    def stop_plot_updates(self):
        """停止绘图更新定时器"""
        if self.plot_update_timer is not None:
            self.root.after_cancel(self.plot_update_timer)
            self.plot_update_timer = None
    
    def update_plots_loop(self):
        """绘图更新循环"""
        self.update_plots()
        if self.is_running:
            self.plot_update_timer = self.root.after(self.plot_update_interval, self.update_plots_loop)
    
    def update_plots(self):
        """更新图形显示"""
        # 检查数据缓冲区是否有数据
        if len(self.ch1_data) == 0 or len(self.ch2_data) == 0:
            return
        
        # 准备时间轴数据
        time_axis = list(range(len(self.ch1_data)))
        ch1_data = list(self.ch1_data)
        ch2_data = list(self.ch2_data)
        
        # 打印调试信息
        # print(f"更新图形: CH1数据点数量={len(ch1_data)}, CH2数据点数量={len(ch2_data)}")
        # print(f"CH1数据范围: {min(ch1_data)} - {max(ch1_data)}")
        # print(f"CH2数据范围: {min(ch2_data)} - {max(ch2_data)}")
        
        # 更新ECG通道
        self.line1.set_data(time_axis, ch1_data)
        
        # 总是更新轴限制，确保数据可见
        x_min, x_max = 0, len(time_axis) - 1
        y_min, y_max = min(ch1_data), max(ch1_data)
        self.ax1.set_xlim(x_min, x_max)
        # 确保y轴范围不会为0
        if y_min == y_max:
            self.ax1.set_ylim(y_min - 1, y_max + 1)
        else:
            self.ax1.set_ylim(y_min - 0.05 * (y_max - y_min), y_max + 0.05 * (y_max - y_min))
        
        # 更新CH2通道
        self.line2.set_data(time_axis, ch2_data)
        
        # 总是更新轴限制，确保数据可见
        x_min, x_max = 0, len(time_axis) - 1
        y_min, y_max = min(ch2_data), max(ch2_data)
        self.ax2.set_xlim(x_min, x_max)
        # 确保y轴范围不会为0
        if y_min == y_max:
            self.ax2.set_ylim(y_min - 1, y_max + 1)
        else:
            self.ax2.set_ylim(y_min - 0.05 * (y_max - y_min), y_max + 0.05 * (y_max - y_min))
        
        # 更新计算值
        combined_values = [(v1 + v2) / 2 if v1 != 0 or v2 != 0 else 0 
                          for v1, v2 in zip(self.cv1_data, self.cv2_data)]
        self.line3.set_data(time_axis, combined_values)
        
        # 总是更新轴限制，确保数据可见
        x_min, x_max = 0, len(time_axis) - 1
        y_min, y_max = min(combined_values), max(combined_values)
        self.ax3.set_xlim(x_min, x_max)
        if y_min == y_max:
            self.ax3.set_ylim(y_min - 1, y_max + 1)
        else:
            self.ax3.set_ylim(y_min - 0.05 * (y_max - y_min), y_max + 0.05 * (y_max - y_min))
        
        # 更新画布
        self.canvas.draw()
    
    def run(self):
        """运行应用程序"""
        self.root.mainloop()

if __name__ == "__main__":
    app = SyncAcquisition()
    app.run()
