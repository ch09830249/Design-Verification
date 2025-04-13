## AHB 總線特點
* **高速總線，高性能**
* 具有兩級流水操作，包括**地址週期**和**資料週期**的兩級管線處理 (Pipeline)
* 第一個週期讀地址，第二個週期寫數據，用流水線操作處理，在**第二個週期寫數據的同時讀另一個地址**，這樣在下一個週期就可以直接寫數據，讀地址寫數據同時進行，這樣兩週期的操作在流水線開始後每週期都能寫一個數據
![image](https://github.com/user-attachments/assets/866bd692-0b1e-45ba-9b0f-164a0f9d3b90)
* AHB 可以支援多個總線主設備（最多 16 個）
* 也支援 burst 傳輸。就是一次 burst 傳輸，一次傳輸一串數據，數據長度為 burst length
* 總線頻寬：8、16、32、64、128 bits。採用上升沿觸發操作
## AHB 組成
* **AHB 主設備 (master)**
  * 初始化一次讀取/寫入操作。**某一時刻只允許一個主設備使用總線**。例如 CPU、DMA、DSP、LCDC 等。
* **AHB 從裝置 (slave)**
  * 響應一次讀取/寫入操作。**透過位址映射來選擇使用哪一個從設備**。外部記憶體控制 EMI、APB bridge 等。
* **AHB 仲裁器 (arbiter)** => (決定哪個 master 可以做事)
  * 因為總線上只允許一個 master 訪問，所以**在多個 master 同時申請總線的時候就會引起衝突**，**這就需要仲裁器來選擇給哪個 master 總線的控制權**。
  * 但在 AMBA 協定中沒有定義仲裁演算法，所以具體分配可以自己客製化，循環優先也好 (Round Robin)、設定優先順序也好 (Priority)，都可以自己客製。
* **AHB 譯碼器 (decoder)** => (確定 master 要對哪個 slave 做事)
  * 透過地址 decode 來決定哪一個從設備。它必須知道地址 map 訊息，知道後就會分析總線上的 address 是什麼值，落在那個 slave 的區域，就會把對應 slave 的 HSEL 訊號拉高 (意即 select 該 slave)。而作為 slave 而言，他就看自己的 HSEL 訊號是否被譯碼器拉高來判斷自己是否要工作。
# AHB 訊號
![image](https://github.com/user-attachments/assets/b577dfd8-8f3f-4f04-b23b-421554ab5f47)
* 這裡的訊號都是 H 開頭，因為是 AHB 匯流排的訊號，如果是 APB 的話，就會是 P 開頭。
* HRESETn 表示低電位有效的複位
* HADDR[31:0] 是 **32 bits 系統位址匯流排** (For Address)
* HWDATA[31:0] 寫入資料匯流排，從主裝置寫到從裝置
* HRDATA[31:0] 讀取資料匯流排，從從裝置讀到主裝置
* HTRANS 是指目前**傳輸的狀態**，分為 **IDLE、BUSY、NONSEQ 和 SEQ**
  * 00：IDLE, 主設備佔據總線，但沒進行傳輸，兩次 burst 中間主設備沒準備好的話發 IDLE
  * 01：BUSY, 主設備佔用總線，但在 burst 傳輸過程中還沒準備好進行下一次傳輸，一次 burst 傳輸中間主設備發 BUSY
  * 10：NONSEQ, 表示一次單一數據的傳輸，或**一次 burst 傳輸的第一個數據**，位址和控制訊號與上一次傳輸無關
  * 11：SEQ, **顯示 burst 傳輸接下來的數據**，地址和上一次傳輸的地址是相關的
* HWRITE 訊號表示讀寫狀態，**HWRITE=1** 時表示**寫**，**=0** 時表示**讀取**狀態
* HSIZE 指 BUS 的寬度目前傳輸大小，HSIZE=000 時為 8bit，HSIZE=001 時為 16bit，HSIZE=010 時為 32bit，以此類推
* HBURST 指傳輸的 burst 類型，總共有 8 種：SINGLE、INCR、WRAP[4|8|16]、INCR[4|8|16] (後續解釋 INCR 和 WRAP)
* HSELx 用來選擇 slave
* HRESP 是從設備發給主設備的匯流排傳輸狀態，有四種狀態：ERROR、OKAY、SPLIT 和 RETRY
  * RETRY 和 SPLIT 有區別。
    * RETRY 不會影響被拒絕的 master 的優先級，但是如果用 SPLIT 拒絕了當前的 master，arbiter 會把目前被拒絕的 master 優先級降低。
* HREADY為高：**從設備指出傳輸結束**；**為低：從設備需要延長傳輸週期**。
# 一次無需等待的 AHB 傳輸
![image](https://github.com/user-attachments/assets/e67f169b-fd1e-4a3b-b6d6-82cb5c458e27)
* 寫入操作 HADDR 就是寫位址，把 HWDATA 訊號寫入，如果是讀，HADDR 就是讀取位址，採樣 HRDATA 訊號讀出資料。
* 如果 slave 沒有準備好接受訊號，那麼傳輸的資料就會延長到 HREADY 被拉高。但 master 不會一直無限等 slave，**最多等 16 個週期**，slave 在 HRESP 訊號裡回傳 RETRY。
![image](https://github.com/user-attachments/assets/d00763c9-afb8-4d4c-9892-814c7cddaa35)
![image](https://github.com/user-attachments/assets/c2870bb0-0b12-433d-9a76-f04fc2a294de)
但上面這種傳輸速度不夠快，所以 AHB 採用的其實是 pipeline 結構的資料傳輸，如下圖
![image](https://github.com/user-attachments/assets/e9f75834-6e3e-469c-9ee3-427db07afd45)
這樣一次傳輸一個地址，傳輸一個數據，那麼每來一次傳輸，都要 decode 一次，效率很低，提高傳輸效率的方法就是 burst 傳輸，每一次 burst 傳輸只需要 decode 一次，提高數據傳輸效率。
# Burst
## Example
假設你要從記憶體讀 4 筆資料，地址從 0x1000 開始。
* 使用 burst：
  * 控制訊號設定一次
  * 傳輸流程：0x1000 → 0x1004 → 0x1008 → 0x100C（假設每筆資料 4 bytes）
* 使用非-burst：
  * 每筆都需要重新設定控制訊號，效能較差
* AHB BURST 操作 4 beat、8 beat、16 beat、單字節傳輸、未定義長度傳輸 (注意這裡是 beat，不是 bit，表示傳輸次數)
  * **1 beat = 一筆資料傳輸**
  * beat 的大小 = 資料匯流排（data bus）的寬度常
    * 見資料寬度：
      * 32-bit → 1 beat = 4 bytes
      * 64-bit → 1 beat = 8 bytes
      * 128-bit → 1 beat = 16 bytes
      * 甚至可能是 256-bit 或更大
* 支援 incrementing 和 wrapping (回環) 兩種 burst 傳輸
  * incrementing burst 地址是上次的傳輸地址加一。
  * Wrapping burst（回環）：例如4beat的wrapping burst字傳輸（4byte）
    * Wrapping Burst 是什麼？
      * Wrapping Burst 是一種地址在特定範圍內循環（wrap around） 的 burst 傳輸方式。**當 burst 長度達到設定值後，地址會回到 burst 開始的對齊邊界繼續傳輸**。這種方式常見於 cache line fill 的應用情境。(當 CPU 從 cache miss 時，要去記憶體抓一整個 cache line)
      * EX1:
        假設你有一個 4-beat 的 wrapping burst，每 beat 傳 4 bytes（data bus 為 32-bit）：  
        那總共是 4 × 4 = 16 bytes  
        起始地址是 0x24，這個地址不在 16 bytes 對齊邊界上  
        wrapping burst 會「包回」到對齊的範圍，地址變成  
```
        地址傳輸順序（假設從 0x24 開始）：
0x24 → 0x28 → 0x2C → 0x20（回繞到 16-byte 對齊的起點）
```
![image](https://github.com/user-attachments/assets/05c06048-7e1d-491d-91ad-2960cd39c3bd)
WRAP4 的位址回環倍數是 0x10，WRAP8 的位址回環倍數是 0x20，WRAP16 的位址回環倍數是 0x40。因為HSIZE = 010，所以每次地址的遞增都是 4 個，也就是 4byte。上面就是 8 種burst型。Type 後面的數字表示傳輸的資料個數，也就是beat。  
下面的是 INCR8 的波形圖：  
![image](https://github.com/user-attachments/assets/b09ff790-b111-4a98-8ccf-887db48ace4f)  
下面的是 WRAP8 的波形圖：  
![image](https://github.com/user-attachments/assets/e8c16d32-632c-46f3-9775-eaea864d5cb2)
上面是比較簡略的波形圖用來示意 INCR 和 WRAP 的差別，下面的 INCR4 和 WRAP4 的波形圖就正規一點了。  
![image](https://github.com/user-attachments/assets/a88fb8f4-78d0-4872-be82-28fd02e3ea70)  
看 HBURST 類型，上圖為 INCR4，下圖為 WRAP4。  
![image](https://github.com/user-attachments/assets/ceb17d90-3607-4055-8341-aa9abf3e01f5)
好，看了那麼多波形，對不同的 burst 傳輸應該有比較深的認識了。這裡還要補充一些 burst 的特色。**burst 傳輸不能超過 1K 邊界**。一個從設備最小的位址間隙是 1KB。 burst 不能越過 1KB 的邊界，那遇到邊界該如何處理呢：  
非序列 ->序列-> 1KB邊界 ->非序列 ->序列 
![image](https://github.com/user-attachments/assets/ef0454ca-a286-4496-8bd6-436f9c9c279c)
如圖，傳輸到 0x400 的倍數的時候就要再發起一個 burst，不然就超過 1K 邊界了（4*16Byte^2=1024Byte=1KB） 
![image](https://github.com/user-attachments/assets/2edfa778-d306-4ff2-8b51-e0cfdf0ba290)
HSELx: 由 decoder 輸出，選擇從設備，指出由主設備選擇的從設備。由地址譯碼器來提供選擇訊號。一個從設備應該至少佔用 1KB 的儲存空間 (0x400 位址的倍數就得 NONSEQ）。需要一個額外的預設從設備來映射其他的儲存位址（default：），可以表現為當 addr 落在某個範圍的時候，HSELx 等於多少，當 addr 落在另一個範圍的時候 HSELx 又等於多少，其他情況下（else or default），HSELx 等於多少（有點類似於組合邏輯不能綜合出 latch，涉及每一個分支都得被等於的意思）。  
第一個 MUX 由 Arbiter 仲裁，選擇 HADDR 為哪個 master 的位址，然後把 HADDR 輸入到 Decoder 中，選擇把哪個 slave 的 HSEL 拉高。
![image](https://github.com/user-attachments/assets/1c9175a6-8314-4fcf-88db-531fb24c31ac)  
如果 slave 被 Decoder 選中，也就是 slave 的 HSEL 被拉高，從裝置必須回應這次傳輸！
 * slave可能回傳的回應：
   * 1. 完成這次傳輸（OKAY）
   * 2. 插入等待狀態（HREADY）
   * 3. 發出錯誤訊號表示這次傳輸失敗（ERROR）
   * 4. 延時傳輸，使得匯流排可用於其他傳輸（RETRY、SPLIT）
HRESP[1:0] ：
00：OKAY   單週期響應  
01：ERROR  兩週期響應  
10：RETRY  兩週期響應  
11：SPLIT  兩週期響應  
總線的流水特性，需要從設備兩個週期的響應。可以使得主設備有足夠的時間處理下一次傳輸。SPLIT 和 RETRY 的差別在於使用 SPLIT 拒絕請求後，會降低 master 在 Arbiter 的優先權。具體 Arbiter 用什麼優先策略可以自己客製。總線主設備應該用同樣的方式處理 RETRY 響應和 SPLIT 響應。  
## RETRY 響應
![image](https://github.com/user-attachments/assets/733d632e-8b33-4f53-a300-d4ffe2951e45)  
RETRY 要保持兩個 cycle 。如果錯誤的話，也就是回傳 HRESP 不是 OKAY，那 master 的 HTRANS 就要進入 IDLE 狀態，所以需要額外一個週期來進入 NONSEQ 狀態。資料匯流排不是三態匯流排，讀匯流排和寫匯流排是分開的。什麼是三態呢？只有在PAD部分，有三個埠INPUT、OUTPUT、INOUT，在這些輸出埠上會有三態狀態，在匯流排內部是沒有三態的。印第安序，印第安序用來表示總線有效的位數。主設備和從設備應該採用同樣的印第安序，不支援動態的印第安序，在AMBA協定中沒有定義。
![image](https://github.com/user-attachments/assets/81da36f1-5f49-42a0-b5df-06e254ac665c)  
32bit小印第安序資料匯流排有效位元組  
![image](https://github.com/user-attachments/assets/a7e4eb4e-8b95-412e-bdc9-30f3e5f09a8c)
32bit大印第安序資料匯流排有效位元組
# AHB 仲裁訊號
![image](https://github.com/user-attachments/assets/4ddb35c9-934d-4bde-bcb3-8fd97f79999b)
因為最多支援 16 個 master，所以 HMASTER 只需要四個 bit 就夠了。
* HBUSREQ 匯流排請求，master 發送匯流排請求，然後 Arbiter 允許的話就回傳 GRANT 訊號
* HLOCKx 高電位：主裝置要求鎖定總線，因為不希望 master 原本要傳送一百個資料的，結果中途被打斷了，所以需要把總線lock住
* HGRANTx 指出主設備 x 可存取匯流排，主設備 x 控制匯流排條件：HGRANTx = 1 且 HREADY = 1
* HMASTER[3:0] 指出哪個主設備正在進行傳輸
* HMASTLOCK 指出主設備正在進行一次鎖定傳輸
* HSPLITx[15:0] 從裝置用這個訊號告訴仲裁者哪個主裝置允許重新嘗試一次 split 傳輸，16bit 每一位對應一個主裝置。 ，這裡既有x又有16bit，其中x代表哪一個slave，16bit從來選master，因為經過arbiter後，slave很清楚是哪一個master在請求他，所以如果要拒絕哪一個master的請求，由slave發出會比較準確
# Example
## 沒有等待狀態的 HGRANT 拉高
![image](https://github.com/user-attachments/assets/b6ab6dc0-c942-4e83-8d67-7b7eb00e54a4)  
上圖為沒有等待狀態的 HGRANT 拉高波形圖，HGRANT 訊號一拉高，資料就開始傳輸（沒有等待是因為 HREADY 一直為高），所以 HGRANT 一拉高，滿足 HREADY = 1 且HGRANTx = 1 匯流排就會把控制權交給 HMASTER。但很多時候，HGRANT 拉高的時候，HREADY 並不是1，所以下面的波形圖比較普適性。
## 等待狀態的 HGRANT 拉高
![image](https://github.com/user-attachments/assets/7b7c979c-8d26-4cd5-a857-8975226a63fe)  
Arbiter 在接收到 master 發送的 HBUSREQx 指令後，經過兩個週期給出 GRANTx 指令，然後在 T4 時刻，發現呢 HREADY 並不為高，所以masterx 不能獲得總線控制權，在 T5 時刻，HGRANT 和 HREADY 都為1，masterx 獲得總線控制權，可以傳輸數據，但在 T6 時候 HREADY 在master 用完總線後，需要把總線控制權還回去：
![image](https://github.com/user-attachments/assets/f550d8c4-413e-4076-bc88-0e80d8271f4b)  
對M1來說，市區GRANT之後，還能再發一個地址與資料。 對於M2master來說，在T7時刻拿到資料匯流排控制權後，就可以開始傳輸所以在T7時刻後面的HADDR為一個數、HTRAN為NONSEQ，但是即使這樣傳輸的資料也得到下一個週期才到HWDATA，所以M1這個操作可以把HWDATA匯流排完全利用起來，因為本來M2取得控制權後的第一個週期，資料也浪費了一個週期上，資料
![image](https://github.com/user-attachments/assets/5b533e6a-04a1-48ec-b6ad-67a5c715f733)  
Arbiter 選擇 Master，對 master 來說，master 是知道自己有沒有被GRANT，但是他不知道 HADDR 輸出去後會被發給哪個 slave。 Arbiter選擇哪一個 HMASTER 的 HADDR 送出去，送到哪裡呢？送到 Decoder 解碼，選取哪個 slave。

        補充：對於固定長度的burst傳輸，不必持續請求匯流排。對於未定義長度的burst傳輸，主設備應持續發送HBUSREQ訊號，直到開始最後一次傳輸。

        如果沒有主設備請求匯流排，則給缺省主設備（即default master）GRANT訊號，且HTRANS = IDLE。建議主設備在鎖定匯流排傳輸結束之後插入IDLE傳輸，以重新仲裁優先權、

split傳輸過程：

① 由主設備開始傳輸。

② 如果從設備需要多個週期才能取得數據，則從設備給予一個SPLIT傳輸回應，從設備記錄主設備號碼：HMASTER。接著仲裁器改變主設備的優先權。

③ 仲裁器GRANT其他的主設備，總線主設備移交。

④ 當從設備準備結束本次傳輸，將設定給仲裁器的HSPLITx訊號的對應位元。

⑤ 仲裁器恢復優先權，恢復到發送spilt訊號之前。

⑥ 仲裁器GRANT主設備，這樣主設備可以重新開始傳輸。

⑦ 結束。



        當多個不同的主設備存取同一個從設備，這個從設備發出了SPLIT或RETRY訊號，這時可能發生deadlock死鎖。從設備最多可以接收系統中16個主設備的請求。只需要記錄主設備號碼（忽略位址和控制訊號）。給出RETRY響應的從設備在某一時刻只能由一個主設備存取防止死鎖。
下圖為AHB匯流排的主設備介面  
![image](https://github.com/user-attachments/assets/b032762f-66d4-4415-a9cb-c660b7553bda)
AHB從設備介面： 
![image](https://github.com/user-attachments/assets/5c26247e-a652-4b59-85fe-73011ca6e13c)
AHB Arbiter介面：
![image](https://github.com/user-attachments/assets/fe361ce9-8723-4364-b15d-93266d4453f6)
AHB Decoder介面：
![image](https://github.com/user-attachments/assets/a6b05094-200e-4e2d-a17d-0e44c4f46430)
學習AHB匯流排，需要學會繪製AHB匯流排上四個組成部分的介面框圖，並描述訊號作用。
# AHB匯流排訊號介面
包括 **AHB 主設備**，**AHB 從設備**，**AHB 仲裁器**等。
## AHB主設備
```
interface   ahb_msr_intf #(
parameter   AW  = 32,
            DW  = 32
) (
input   logic       HCLK,
input   logic       HRESETn
);
logic               HGRANT;
logic               HREADY;
HRESP_e             HRESP;
logic   [DW-1:0]    HRDATA;

logic               HBUSREQ;
logic               HLOCK;
HTRANS_e            HTRANS;
logic   [AW-1:0]    HADDR;
logic               HWRITE;
HSIZE_e             HSIZE;
HBURST_e            HBURST;
HPROT_e             HPROT;
logic   [DW-1:0]    HWDATA;


modport m (
    input   HGRANT, HREADY, HRESP, HRDATA,
    output  HBUSREQ, HLOCK, HTRANS, HADDR, HWRITE, HSIZE, HBURST, HPROT, HWDATA
);

modport s (
    input   HBUSREQ, HLOCK, HTRANS, HADDR, HWRITE, HSIZE, HBURST, HPROT, HWDATA,
    output  HGRANT, HREADY, HRESP, HRDATA
);

endinterface: ahb_msr_intf
```
## AHB從設備介面
```
interface   ahb_slv_intf #(
  parameter   AW  = 32,
            DW  = 32
 ) (
input   logic       HCLK,
input   logic       HRESETn
 );
logic               HSEL;
logic   [AW-1:0]    HADDR;
HTRANS_e            HTRANS;
HSIZE_e             HSIZE;
HBURST_e            HBURST;
logic               HWRITE;
HPROT_e             HPROT;
logic   [DW-1:0]    HWDATA;

logic               HREADY;
HRESP_e             HRESP;
logic   [DW-1:0]    HRDATA;


modport m (
    input   HREADY, HRESP, HRDATA,
    output  HSEL, HADDR, HTRANS, HSIZE, HBURST, HWRITE, HPROT, HWDATA
);

modport s (
    input   HSEL, HADDR, HTRANS, HSIZE, HBURST, HWRITE, HPROT, HWDATA,
    output  HREADY, HRESP, HRDATA
);

endinterface: ahb_slv_intf
```
以上為AHB從設備介面。下面對信號進行一一說明。
* HCLK 匯流排時鐘
* HRESETn 總線重設訊號，低電位有效。
* HADDR 位址匯流排，位元組為單位。
* HTRANS[1:0] 傳輸類型，如下：
```
typedef enum logic [1:0] {
    HTRANS_IDLE     = 2'b00,
    HTRANS_BUSY     = 2'b01,
    HTRANS_NONSEQ   = 2'b10,
    HTRANS_SEQ      = 2'b11
} HTRANS_e;
```
* HWRITE 為高表示寫入傳輸，為低表示讀取傳輸。
* HSIZE 傳輸大小，可能的取值定義如下：
```
typedef enum logic [2:0] {
    HSIZE_BYTE      = 3'b000,   // 8bit
    HSIZE_HALFWORD  = 3'b001,   // 16bit
    HSIZE_WORD      = 3'b010,   // 32bit
    HSIZE_DWORD     = 3'b011,   // 64bit
    HSIZE_QWORD     = 3'b100,   // 128bit
    HSIZE_OWORD     = 3'b101,   // 256bit
    HSIZE_HWORD     = 3'b110,   // 512bit
    HSIZE_TWORD     = 3'b111    // 1024bit
} HSIZE_e;
```
* HBURST 突發傳輸類型，突發傳輸模式可以為增量傳輸或回環傳輸。
```
typedef enum logic [2:0] {
   HBURST_SINGLE   = 3'b000,
   HBURST_INCR     = 3'b001,
   HBURST_WRAP4    = 3'b010,
   HBURST_INCR4    = 3'b011,
   HBURST_WRAP8    = 3'b100,
   HBURST_INCR8    = 3'b101,
   HBURST_WRAP16   = 3'b110,
   HBURST_INCR16   = 3'b111
 } HBURST_e;
```
* HPROT 提供匯流排存取的額外資訊並且主要是打算給那些希望執行某種保護等級的模組
使用的。這個訊號指示目前傳輸是否為預取指或資料傳輸，同時也表示傳輸是保護模式存取還是使用者模式存取。對具有記憶體管理單元的匯流排主機而言這些訊號也用來指示目前傳輸是高速緩存的（cache）還是緩衝的（buffer）。定義如下：
```
//   cacheable   |   bufferable   | privileged |  data
// not-cacheable | not-bufferable |    user    | opcode
typedef enum logic [3:0] {
  HPROT_NNUO      = 4'b0000,
  HPROT_NNUD      = 4'b0001,
  HPROT_NNPO      = 4'b0010,
  HPROT_NNPD      = 4'b0011,
  HPROT_NBUO      = 4'b0100,
  HPROT_NBUD      = 4'b0101,
  HPROT_NBPO      = 4'b0110,
  HPROT_NBPD      = 4'b0111,
  HPROT_CNUO      = 4'b1000,
  HPROT_CNUD      = 4'b1001,
  HPROT_CNPO      = 4'b1010,
  HPROT_CNPD      = 4'b1011,
  HPROT_CBUO      = 4'b1100,
  HPROT_CBUD      = 4'b1101,
  HPROT_CBPO      = 4'b1110,
  HPROT_CBPD      = 4'b1111
} HPROT_e;
```
* HWDATA 寫資料。
* HSELx 從機選擇。
* HRDATA 讀取資料。
* HREADY 為高時表示匯流排傳輸完成。
* HRESP 傳輸對應訊號，表徵傳輸狀態，定義如下：
```
typedef enum logic [1:0] {
   HRESP_OKAY      = 2'b00,
   HRESP_ERROR     = 2'b01,
   HRESP_RETRY     = 2'b10,
   HRESP_SPLIT     = 2'b11
} HRESP_e;
```
HSPLITx 16位元訊號，指示仲裁器匯流排主設備應該被允許重試一個分塊傳輸，每一位對應一個匯流排主機。

以下訊號與仲裁器相關：

HBUSREQx 總線主設備x請求申請總線控制權。最多16個主設備。

HLOCKx 匯流排鎖定要求，其他主裝置無法或仲裁器授權。

HGRANTx 表示目前主設備為優先順序最高的主設備。

HMASTER 仲裁器訊號表示正在執行傳輸或支援分塊傳輸的從裝置傳輸的主設備號碼。

HMASTLOCK 主設備正在執行鎖定順序的傳輸。

AHB 互聯矩陣：
```
module ahb_matrix # (
    parameter   WIDTH   = 32,
                NMSR    = 4,
                NSLV    = 16
) (
    input   logic   HCLK,
    input   logic   HRESETn,
    ahb_msr_intf.s  ahbmv[NMSR],
    ahb_slv_intf.m  ahbsv[NSLV]
);

localparam  NMSRV   = $clog2(NMSR),
            NSLVV   = $clog2(NSLV);

logic               HBUSREQx[NMSR];
logic               HGRANTx[NMSR];
logic               HREADY;
HRESP_e             HRESP;
logic   [WIDTH-1:0] HRDATA;

logic               HSEL[NSLV];
logic   [31:0]      HADDR;
logic               HWRITE;
HTRANS_e            HTRANS;
HSIZE_e             HSIZE;
HBURST_e            HBURST;
HPROT_e             HPROT;
logic   [WIDTH-1:0] HWDATA;

logic   [NMSRV-1:0] HMASTER, HMASTERd;
logic   [NSLVV-1:0] HSLAVE, HSLAVEd;
logic               errslv;

genvar              i;


struct {
    logic   [WIDTH-1:0] HADDR   [NMSR];
    logic               HWRITE  [NMSR];
    HTRANS_e            HTRANS  [NMSR];
    HSIZE_e             HSIZE   [NMSR];
    HBURST_e            HBURST  [NMSR];
    HPROT_e             HPROT   [NMSR];
    logic   [WIDTH-1:0] HWDATA  [NMSR];
} ahbmd;

struct {
    logic   [WIDTH-1:0] HRDATA  [NSLV];
    logic               HREADY  [NSLV];
    HRESP_e             HRESP   [NSLV];
} ahbsd;


generate
    for (i = 0; i < NSLV; i++) begin: ahbsv_loop
        assign ahbsv[i].HSEL    = HSEL[i];
        assign ahbsv[i].HADDR   = HADDR;
        assign ahbsv[i].HWRITE  = HWRITE;
        assign ahbsv[i].HTRANS  = HTRANS;
        assign ahbsv[i].HSIZE   = HSIZE;
        assign ahbsv[i].HBURST  = HBURST;
        assign ahbsv[i].HPROT   = HPROT;
        assign ahbsv[i].HWDATA  = HWDATA;
    end
endgenerate

generate
    for (i = 0; i < NMSR; i++) begin: ahbmv_loop
        assign HBUSREQx[i]      = ahbmv[i].HBUSREQ;
        assign ahbmv[i].HGRANT  = HGRANTx[i];
        assign ahbmv[i].HREADY  = HREADY;
        assign ahbmv[i].HRESP   = HRESP;
        assign ahbmv[i].HRDATA  = HRDATA;
    end
endgenerate

generate
    for (i = 0; i < NMSR; i++) begin: ahbmd_loop
        assign ahbmd.HADDR[i]  = ahbmv[i].HADDR;
        assign ahbmd.HWRITE[i] = ahbmv[i].HWRITE;
        assign ahbmd.HTRANS[i] = ahbmv[i].HTRANS;
        assign ahbmd.HSIZE[i]  = ahbmv[i].HSIZE;
        assign ahbmd.HBURST[i] = ahbmv[i].HBURST;
        assign ahbmd.HPROT[i]  = ahbmv[i].HPROT;
        assign ahbmd.HWDATA[i] = ahbmv[i].HWDATA;
    end
endgenerate

assign  HADDR   = ahbmd.HADDR[HMASTER];
assign  HWRITE  = ahbmd.HWRITE[HMASTER];
assign  HTRANS  = ahbmd.HTRANS[HMASTER];
assign  HSIZE   = ahbmd.HSIZE[HMASTER];
assign  HBURST  = ahbmd.HBURST[HMASTER];
assign  HPROT   = ahbmd.HPROT[HMASTER];
assign  HWDATA  = ahbmd.HWDATA[HMASTERd];

generate
    for (i = 0; i < NSLV; i++) begin: ahbsd_loop
        assign ahbsd.HRDATA[i] = ahbsv[i].HRDATA;
        assign ahbsd.HREADY[i] = ahbsv[i].HREADY;
        assign ahbsd.HRESP[i]  = ahbsv[i].HRESP;
    end
endgenerate

assign  HRDATA  = ahbsd.HRDATA[HSLAVEd];
assign  HREADY  = errslv ? 1'b1 : ahbsd.HREADY[HSLAVEd];
assign  HRESP   = errslv ? HRESP_OKAY : ahbsd.HRESP[HSLAVEd];


always_ff @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn)
        HSLAVEd <= '0;
    else if (HREADY)
        HSLAVEd <= HSLAVE;
end

ahb_arbiter #(
    .NMSR       (NMSR)
) ahb_arbiter (
    .HCLK       (HCLK),
    .HRESETn    (HRESETn),
    .HBUSREQx   (HBUSREQx),
    .HTRANS     (HTRANS),
    .HBURST     (HBURST),
    .HRESP      (HRESP),
    .HREADY     (HREADY),
    .HMASTER    (HMASTER),
    .HMASTERd   (HMASTERd),
    .HGRANTx    (HGRANTx)
);

ahb_decoder #(
    .NSLV       (NSLV)
) ahb_decoder (
    .HADDR      (HADDR),
    .HSEL       (HSEL),
    .HSLAVE     (HSLAVE),
    .errslv     (errslv)
);

endmodule: ahb_matrix
```
（二）AHB匯流排工作時序：  
無須多言，看圖。
![image](https://github.com/user-attachments/assets/a5c5e48b-b15d-4f76-a3a4-f4c2a47d589e)  
基本傳輸模式  
![image](https://github.com/user-attachments/assets/e693d4cb-83ee-43b4-a157-187b4b5b2eae)  
多重傳輸  
![image](https://github.com/user-attachments/assets/fda801e9-a586-4eeb-bd6e-27a7e9090e0e)  
使用傳輸類型  
![image](https://github.com/user-attachments/assets/cd6e4259-29dc-4a68-8792-a7534879d659)  
增量突發傳  
![image](https://github.com/user-attachments/assets/11cf8331-5e7a-4ed3-a780-364b0c0149b8)  
回環突發傳輸  
![image](https://github.com/user-attachments/assets/cc9001b6-b2a6-4884-80fa-20bf6b25e057)  
未定義長度的增量突發傳輸  
# Reference
https://aijishu.com/a/1060000000135497  
https://aijishu.com/a/1060000000299181  
https://aijishu.com/a/1060000000229903  
https://www.bilibili.com/opus/639338820199776256
