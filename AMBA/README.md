# AMBA
* **系統晶片中各個模組之間的連接通訊就通過匯流排**，總線就作為子系統之間共享的通訊鏈路。總線可以理解為數據傳輸的協議，大家都按照這種協議 (AHB、APB、AXI) 來傳數據，這樣各個模組之間就不會出錯，尤其是很多時候別人買你的IP，你要保證人家買過去能用起來，那就需要一個規範來統一標準，我們稱之為總線。
* 總線的優點就是成本低，方便使用。缺點也很明顯，就是會造成效能瓶頸，也正是因為這個所以匯流排協定一直在更新，到現在的 AXI4，讀寫資料通道分開，增加了資料的頻寬。
* **AMBA 全名為 Advanced Microcontroller Bus Architecture** ，即片上匯流排協議標準 。AMBA協定是與製程無關的，沒有電氣特性，而是一種協定。總共定義了**三種**總線：
  * **AHB** (Advanced High-Performance Bus) (先進高效能匯流排, 用於高效能系統)
  * ASB（Advanced System Bus）用的很少
  * **APB** (Advanced Peripheral Bus) (進階週邊匯流排, 用於低速週邊)
* AMBA發展歷史：
  * AMBA1.0：ASB 和 APB
  * AMBA2.0: AHB、ASB 和 APB
  * AMBA3.0：**AMBA 高階可擴充介面 (AXI)**
  * AMBA4.0：....
## AHB 總線特點
* **高速總線，高性能**
* 具有兩級流水操作，包括**地址週期**和**資料週期**的兩級管線處理
* 第一個週期讀地址，第二個週期寫數據，用流水線操作處理 (Pipeline)，在**第二個週期寫數據的同時讀另一個地址**，這樣在下一個週期就可以直接寫數據，讀地址寫數據同時進行，這樣兩週期的操作在流水線開始後每週期都能寫一個數據
![image](https://github.com/user-attachments/assets/866bd692-0b1e-45ba-9b0f-164a0f9d3b90)
* AHB 可以支援多個總線主設備（最多 16 個）
* 也支援 burst 傳輸。就是一次 burst 傳輸，一次傳輸一串數據，數據長度為 burst length
* 總線頻寬：8、16、32、64、128bits。採用上升沿觸發操作
## APB 總線特性
* **低速匯流排，低功耗**
* 介面簡單。在 bridge 中鎖存位址訊號和控制訊號。適用於多種週邊，採用上升沿觸發操作。
## AHB 組成
* **AHB 主設備 (master)**
  * 初始化一次讀取/寫入操作。**某一時刻只允許一個主設備使用總線**。例如 CPU、DMA、DSP、LCDC 等。
* **AHB 從裝置 (slave)**
  * 響應一次讀取/寫入操作。**透過位址映射來選擇使用哪一個從設備**。外部記憶體控制 EMI、APB bridge 等。
* **AHB 仲裁器 (arbiter)**
  * 因為總線上只允許一個 master 訪問，所以**在多個 master 同時申請總線的時候就會引起衝突**，**這就需要仲裁器來選擇給哪個master總線的控制權**。
  * 但在 AMBA 協定中沒有定義仲裁演算法，所以具體分配可以自己客製化，循環優先也好、設定優先順序也好，都可以自己客製。
* **AHB譯碼器 (decoder)**
  * 透過地址譯碼來決定哪一個從設備。它必須知道地址 map 訊息，知道後就會分析總線上的 address 是什麼值，落在那個 slave 的區域，就會把對應 slave 的 HSEL 訊號拉高 (意即 select 該 slave)。而作為 slave 而言，他就看自己的 HSE L訊號是否被譯碼器拉高來判斷自己是否要工作。


## APB 組成


# Reference
AHB總線筆記（一）: https://www.bilibili.com/opus/639338820199776256  
AHB總線筆記（二）: https://www.bilibili.com/opus/639615918584889361?spm_id_from=333.1387.0.0
AHB匯流排筆記（三）附AMBA2.0面試提問: https://www.bilibili.com/opus/639640082077188135?spm_id_from=333.1387.0.0
