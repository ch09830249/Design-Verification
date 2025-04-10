**Advanced Microcontroller Bus Architecture, 即AMBA，是ARM公司提出的總線規範，被許多SoC設計所採用，常用的實作有AHB（Advanced High-Performance Bus）和APB（Advanced Peripheral Bus）。 AHB用於高效能係統，APB用於低速週邊。以下程式碼實例使用的是SystemVerilog描述。**
（一）AHB匯流排訊號介面：
　　包括AHB主設備，AHB從設備，AHB仲裁器等。
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
以上為AHB主設備介面。
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

　　HCLK 匯流排時鐘

　　HRESETn 總線重設訊號，低電位有效。

　　HADDR 位址匯流排，位元組為單位。

　　HTRANS[1:0] 傳輸類型，如下：
```
typedef enum logic [1:0] {
    HTRANS_IDLE     = 2'b00,
    HTRANS_BUSY     = 2'b01,
    HTRANS_NONSEQ   = 2'b10,
    HTRANS_SEQ      = 2'b11
} HTRANS_e;
```
HWRITE 為高表示寫入傳輸，為低表示讀取傳輸。

　　HSIZE 傳輸大小，可能的取值定義如下：
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
HBURST 突發傳輸類型，突發傳輸模式可以為增量傳輸或回環傳輸。
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
# Reference
https://aijishu.com/a/1060000000135497  
https://aijishu.com/a/1060000000299181  
https://aijishu.com/a/1060000000229903  
https://www.bilibili.com/opus/639338820199776256
