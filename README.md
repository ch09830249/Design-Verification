# Design-Verification
## System Verilog 環境架設
- **Local environment:**
  ![image](https://github.com/user-attachments/assets/ec80103c-f504-4db7-a466-33e12b753d41)
  https://ithelp.ithome.com.tw/m/articles/10315791  
  https://www.dcard.tw/f/nctu/p/239947030  
  https://www.dcard.tw/f/nctu/p/235935287
  - **編譯與執行**
  ```
  iverilog -o YYY XXX.sv  
  iverilog -o YYY -g2012 XXX.sv (https://electronics.stackexchange.com/questions/640456/syntax-error-iverilog)
  vvp YYY
  ```
  - Current supported generations  
  ![image](https://github.com/user-attachments/assets/ce38d515-bda4-4869-b639-a58ed86026a8)
- **Online environment:**
  ![image](https://github.com/user-attachments/assets/bad19595-3b14-490b-935c-6a4cfa8c5e65)
  https://www.youtube.com/watch?v=f9uwtAax4v0  
- **波形**  
  選取 Open EPWave after run  
  ![481796210_614526054679241_8146042943903981013_n](https://github.com/user-attachments/assets/3ff5448e-e3ac-4010-bd36-cc7783d986d8)
  ![483264664_1216799453199195_1258006194081326055_n](https://github.com/user-attachments/assets/15a664de-0fc3-4ecc-80cd-a2775550d0c6)
## Reference
路科验证: https://www.bilibili.com/video/BV1k7411H7Jo/  
https://www.youtube.com/watch?v=_QjZ06eg3cY&list=PL40xmtPvboRs6Ng_1Q_V-1MdJH50A6Ulz&index=4  
ChipVerify(SystemVerilog): https://www.chipverify.com/systemverilog  
ChipVerify(UVM): [https://www.chipverify.com/systemverilog  ](https://www.chipverify.com/tutorials/uvm)


# Tmp
## Verilog 和 SystemVerilog 的差別
| 項目            | Verilog            | SystemVerilog                                                 | 備註                         |
| ------------- | ------------------ | ------------------------------------------------------------- | -------------------------- |
| **語言類型**      | 專注於硬體描述，語法簡單，但驗證能力弱             | Verilog 的超集 (HDL + Verification featuresVerilog)，加入了物件導向、驗證功能、抽象化建模等現代設計特性，適合大型 ASIC/FPGA 開發與驗證                        | SystemVerilog 向下兼容 Verilog |
| **RTL 設計**    | ✅ 支援               | ✅ 支援                                                          | 兩者都可描述數位電路                 |
| **資料型別**      | reg, wire, integer | logic, bit, byte, shortint, int, longint, struct, union, enum | SystemVerilog 型別更強，支援結構化資料 |
| **強型別檢查**     | ❌                  | ✅                                                             | SystemVerilog 可以檢查型別不匹配    |
| **模組間連接**     | port 列表            | interface、modport                                             | interface 簡化大型設計訊號連接       |
| **程式語言特性**    | ❌                  | class, inheritance, polymorphism                              | 支援物件導向設計與驗證                |
| **迴圈與資料操作**   | for, while         | for, while, foreach, queue, dynamic array, associative array  | SystemVerilog 支援更高級資料操作    |
| **隨機化**       | ❌                  | ✅ random(), constraint                                        | 主要用於驗證 testbench           |
| **斷言**        | ❌                  | ✅ assert, assume, cover                                       | 支援形式化驗證                    |
| **模組參數化**     | parameter          | parameter, localparam, type parameter                         | SystemVerilog 更靈活          |
| **Testbench** | ❌（需額外手寫）           | ✅ 支援 class-based testbench, UVM/OVM                           | 大型驗證環境專用                   |
| **事件控制**      | always, initial    | always_comb, always_ff, always_latch, initial                 | SystemVerilog 提供更明確時序語意    |
| **封裝與介面**     | ❌                  | package, import                                               | 支援程式化模組封裝                  |
| **系統函式**      | $display, $monitor | $display, $monitor, $clog2, $bitstoreal, $urandom             | SystemVerilog 有更多方便函式      |

## 3️⃣ 主要改進方向

* 驗證能力強化
  * SystemVerilog 支援 class、interface、random、constraint、assertion，讓 testbench 更容易寫和維護  
  * 適合 UVM 驗證環境  
* 程式語言化
  * SystemVerilog 引入了許多程式語言特性（如類別、繼承、多型、函式覆寫等），讓設計者可以用更抽象的方法描述硬體  
* 資料型別與結構化
  * 可以定義 struct、union、enum，讓程式更清晰、可讀性更高  
* 模組介面化
  * interface 可以簡化模組間訊號連接，避免傳統 Verilog 需要大量 port 列表  
