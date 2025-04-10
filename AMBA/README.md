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
* AHB2APB 橋
  * 可以鎖存所有位址、資料和訊號。
  * 進行二級譯碼來產生 APB 從設備選擇訊號，APB 有一個位址空間例如 0x5000_0000~0x6fff_ffff，其中又分為很多小的 APB 位址，例如 APB1~APB5，當 AHB 匯流排上位址落在Bx5000_0000ffffxfff_ffffx6ffffffffx7。 (看下面範例比較清楚)
* APB總線上的所有其他模組都是APB從設備。
## 設備之間的通訊範例
* 拿一個 CPU 控制 DMA 的過程舉例說明設備之間的通訊：
![image](https://github.com/user-attachments/assets/806d01b8-84ae-4598-ba22-0b6a8947f39e)
* DMA 在系統中**主要扮演一個資料搬運的角色**，它可以取代 CPU 做資料遷移
* DMA 有自己的位址空間，表格中的 Address 為偏移位址 offset (0x30000+offset)，從 DMA 基底位址開始的一些暫存器保存的一般為狀態，稱為**狀態暫存器**。
* CPU 控制 DMA 搬移數據，先從 DMA 中讀 DMA 的 Status，如果讀取 DMA 是 ready 狀態，那麼就可以給 DMA 寫的 0x00 位址給 1 (Start)，然後告訴 DMA 資料搬運的起始位址（Source address) 和目的位址（Destination address），然後再告訴DMA搬運資料的數量。
* 之後就可以把搬運資料的工作交給DMA，然後自己騰出手來做別的事。 CPU 控制 DMA 做資料搬運主要可以分為以下步驟：
  * step1: CPU 設定(來源位址)、(目的位址)、（大小）
  * step2: 啟動 DMA
  * step3: DMA 把資料從 memory1 傳送到 memory2
  * step4: DMA 向 CPU 發動中斷請求
  * step5: CPU 檢查 DMA 的狀態
## AMBA 匯流排的互連
![image](https://github.com/user-attachments/assets/04660363-cb87-40a2-b76b-e51f3c7d22bc)
* Arbiter 控制 mux 選擇哪個 master 有效。
* 選取了 master 之後，HADDR 會被**送進 Decoder 判斷選中的是那個 slave**
* 然後把對應 slave 的 **HSEL 訊號拉高**表示 slave 工作
* 接著**讀入位址**和**資料訊號** (PS: 這裡其他的 slave 其實也能看到資料和位址訊號，但因為他們的HSEL訊號沒被拉高，所以不會運作)
**Note**: master 和 slave 中還有一對常用的 master 和 slave，就是 default master 和 default slave。當沒有 master 在工作的時候，就選擇 default master 來控制總線，這個 master 可以直接存取總線而不需要兩個仲裁週期的時間，他是最常用的 master。當沒有 slave 被控制的時候就選擇default slave 來被控制。
# Reference
AHB總線筆記（一）: https://www.bilibili.com/opus/639338820199776256  
AHB總線筆記（二）: https://www.bilibili.com/opus/639615918584889361?spm_id_from=333.1387.0.0
AHB匯流排筆記（三）附AMBA2.0面試提問: https://www.bilibili.com/opus/639640082077188135?spm_id_from=333.1387.0.0
