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

## 4-state logic
| 值     | 意義                  |
| ----- | ------------------- |
| **0** | 邏輯 0                |
| **1** | 邏輯 1                |
| **X** | 不確定（unknown）        |
| **Z** | 高阻抗（high-impedance） |

常見於 RTL 設計、模擬、tri-state bus。
* 典型型別：
  * reg（Verilog）
  * logic（SystemVerilog）
  * wire（大多數情況 4-state）

## 2-state logic
| 值     | 意義   |
| ----- | ---- |
| **0** | 邏輯 0 |
| **1** | 邏輯 1 |

沒有 X、Z 概念。
* 典型型別：
  * bit（SystemVerilog）
  * int、byte 等整數型別（本質上也是 2-state）


| 特性   | reg (4-state)     | bit (2-state)          |
| ---- | ----------------- | ---------------------- |
| 表示值  | 0, 1, X, Z        | 0, 1                   |
| 模擬精度 | 高（可表示未知/浮動）       | 低（未知會被強制為 0/1）         |
| 設計用途 | RTL 設計訊號、時序邏輯     | 不需 X/Z 的資料運算、testbench |
| 硬體對應 | 代表真實硬體行為（線會有 X/Z） | 純軟體運算概念，不存在 X/Z        |
| 效能   | 模擬較慢              | 模擬較快                   |
| 收斂性  | 可能因 X 擴散影響結果      | 無 X，結果確定               |

## =（blocking assignment）
像程式語言的普通賦值，一條語句做完才做下一條。
```
a = b;   // 先做這個
c = a;   // 然後做這個
```
## <=（non-blocking assignment）
像「排隊更新」，不會阻塞下一行。
```
a <= 1;
b <= a;   // 使用 a 的舊值（因為 a 還沒更新）
```

## swap 兩個值
```
a = b;
b = a;
結果：a = b；b = b（不能交換）
```
```
a <= b;
b <= a;
因為兩個都用舊值 → 能正確交換！
```

## m_sequencer 與 p_sequencer 是什麼? 使用情景為何?
1. m_sequencer
  * 由 UVM 自動建立的 sequencer 變數（untyped）
  * 型態為 uvm_sequencer_base
  * 用途：讓 sequence 可以知道「自己是跑在誰的 sequencer 上」
  * 特點
    * 不需要手動宣告
    * 由 UVM_DO、start_item() 等機制自動填入
    * 因為是 base class，所以不能直接使用 sequencer 上特有的 function 或變數

| 名稱              | 說明                             | 何時使用                                                |
| --------------- | ------------------------------ | --------------------------------------------------- |
| **m_sequencer** | UVM 自動提供的 untyped sequencer 變數 | **只需要基本 sequence/sequencer 功能，不需呼叫客製化函式時使用**        |
| **p_sequencer** | 使用者宣告的 typed sequencer handle  | **需要存取 sequencer 的特定變數/方法時（例如：config、mailbox、API）** |
