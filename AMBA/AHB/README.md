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
* **AHB 仲裁器 (arbiter)**
  * 因為總線上只允許一個 master 訪問，所以**在多個 master 同時申請總線的時候就會引起衝突**，**這就需要仲裁器來選擇給哪個master總線的控制權**。
  * 但在 AMBA 協定中沒有定義仲裁演算法，所以具體分配可以自己客製化，循環優先也好 (Round Robin)、設定優先順序也好 (Priority)，都可以自己客製。
* **AHB 譯碼器 (decoder)**
  * 透過地址 decode 來決定哪一個從設備。它必須知道地址 map 訊息，知道後就會分析總線上的 address 是什麼值，落在那個 slave 的區域，就會把對應 slave 的 HSEL 訊號拉高 (意即 select 該 slave)。而作為 slave 而言，他就看自己的 HSEL 訊號是否被譯碼器拉高來判斷自己是否要工作。
# AHB 訊號
![image](https://github.com/user-attachments/assets/b577dfd8-8f3f-4f04-b23b-421554ab5f47)
* 這裡的訊號都是 H 開頭，因為是 AHB 匯流排的訊號，如果是 APB 的話，就會是 P 開頭。
* HRESETn 表示低電位有效的複位
* HADDR[31:0] 是 32 位元系統位址匯流排
* HWDATA[31:0] 寫入資料匯流排，從主裝置寫到從裝置
* HRDATA[31:0] 讀取資料匯流排，從從裝置讀到主裝置
* HTRANS 是指目前傳輸的狀態，分為 **IDLE、BUSY、NONSEQ 和 SEQ**
  * 00：IDLE: 主設備佔據總線，但沒進行傳輸，兩次 burst 中間主設備沒準備好的話發 IDLE
  * 01：BUSY: 主設備佔用總線，但在 burst 傳輸過程中還沒準備好進行下一次傳輸，一次 burst 傳輸中間主設備發 BUSY
  * 10：NONSEQ: 表示一次單一數據的傳輸，或一次 burst 傳輸的第一個數據，位址和控制訊號與上一次傳輸無關
  * 11：SEQ: 顯示 burst 傳輸接下來的數據，地址和上一次傳輸的地址是相關的
* HWRITE 訊號表示讀寫狀態，HWRITE=1 時表示寫，=0 時表示讀取狀態
* HSIZE 指 BUS 的寬度目前傳輸大小，HSIZE=000 時為 8bit，HSIZE=001 時為 16bit，HSIZE=010 時為 32bit，以此類推
* HBURST 指傳輸的 burst 類型，總共有8種：SINGLE、INCR、WRAP[4|8|16]、INCR[4|8|16]
* HSELx 用來選擇 slave
* HRESP 是從設備發給主設備的匯流排傳輸狀態，有四種狀態：ERROR、OKAY、SPLIT 和 RETRY
  * RETRY 和 SPLIT 有區別。
    * RETRY 不會影響被拒絕的 master 的優先級，但是如果用 SPLIT 拒絕了當前的 master，arbiter 會把目前被拒絕的 master 優先級降低。
* HREADY為高：從設備指出傳輸結束；為低：從設備需要延長傳輸週期。
# 一次無需等待的 AHB 傳輸
![image](https://github.com/user-attachments/assets/e67f169b-fd1e-4a3b-b6d6-82cb5c458e27)
* 寫入操作 HADDR 就是寫位址，把 HWDATA 訊號寫入，如果是讀，HADDR就是讀取位址，採樣 HRDATA 訊號讀出資料。
* 如果 slave 沒有準備好接受訊號，那麼傳輸的資料就會延長到 HREADY 被拉高。但 master 不會一直無限等 slave，最多等 16 個週期，slave 在 HRESP 訊號裡回傳 RETRY。
![image](https://github.com/user-attachments/assets/d00763c9-afb8-4d4c-9892-814c7cddaa35)
但上面這種傳輸速度不夠快，所以 AHB 採用的其實是 pipeline 結構的資料傳輸，如下圖
![image](https://github.com/user-attachments/assets/e9f75834-6e3e-469c-9ee3-427db07afd45)
這樣一次傳輸一個地址，傳輸一個數據，那麼每來一次傳輸，都要decode一次，效率很低，提高傳輸效率的方法就是burst傳輸，每一次burst傳輸只需要decode一次，提高數據傳輸效率。
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
