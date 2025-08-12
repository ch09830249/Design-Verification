# Command line
xrun -uvm top_tb.sv dut.sv  
| 部分          | 說明                                                       |
| ----------- | -------------------------------------------------------- |
| `xrun`      | Cadence 的模擬工具 Xcelium 的執行命令。                             |
| `-uvm`      | 啟用 UVM 驗證架構（會自動載入 `uvm_pkg` 等必要庫）。                       |
| `top_tb.sv` | 你的 **測試平台（Testbench）** 的頂層模組，通常負責例化 UVM 環境、DUT，以及啟動測試流程。 |
| `dut.sv`    | 你的 **設計模組（DUT，Design Under Test）**，也就是你想要驗證的電路或模組。       |
