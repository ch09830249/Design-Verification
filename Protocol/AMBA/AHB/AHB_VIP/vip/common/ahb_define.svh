`ifndef AHB_DEFINE_SVH
`define AHB_DEFINE_SVH

`define     D_ADDR_WIDTH        64
`define     D_DATA_WIDTH        32
`define     D_SLV_COUNT         1
`define     D_MEM_SIZE          256

// HTRANS
`define     HTRANS_IDLE         2'b00
`define     HTRANS_BUSY         2'b01
`define     HTRANS_NONSEQ       2'b10
`define     HTRANS_SEQ          2'b11

// HBURST
`define     HBURST_SINGLE       3'b000
`define     HBURST_INCR         3'b001

// HSIZE
`define     HSIZE_BYTE          3'b000
`define     HSIZE_HALFWORD      3'b001
`define     HSIZE_WORD          3'b010

// HRESP
`define     HRESP_OKAY          1'b0
`define     HRESP_ERROR         1'b1

`endif
