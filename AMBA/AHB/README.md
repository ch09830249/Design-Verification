**Advanced Microcontroller Bus Architecture, 即AMBA，是ARM公司提出的總線規範，被許多SoC設計所採用，常用的實作有AHB（Advanced High-Performance Bus）和APB（Advanced Peripheral Bus）。 AHB用於高效能係統，APB用於低速週邊。以下程式碼實例使用的是SystemVerilog描述。**  
（一）AHB匯流排訊號介面： 包括 **AHB主設備**，**AHB從設備**，**AHB仲裁器**等。
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
