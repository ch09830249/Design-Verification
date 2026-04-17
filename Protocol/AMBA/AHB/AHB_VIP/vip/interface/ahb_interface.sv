`ifndef AHB_INTERFACE_SV
`define AHB_INTERFACE_SV

`include "ahb_define.svh"

interface ahb_interface;

    logic                           HCLK;
    logic                           HRESETn;

    // Master Signal
    logic [`D_ADDR_WIDTH-1:0]       HADDR;
    logic [2:0]                     HBURST;
    logic                           HMASTLOCK;
    logic [3:0]                     HPROT;
    logic [2:0]                     HSIZE;
    logic [1:0]                     HTRANS;
    logic [`D_DATA_WIDTH-1:0]       HWDATA;
    logic                           HWRITE;

    // Slave Signal
    logic [`D_DATA_WIDTH-1:0]       HRDATA;
    logic                           HREADY;
    logic                           HRESP;

    // Decoder Signal
    logic [`D_SLV_COUNT-1:0]        HSEL;

    modport master (
        output  HADDR, HBURST, HMASTLOCK, HPROT, HSIZE, HTRANS, HWDATA, HWRITE, HSEL,
        input   HRDATA, HREADY, HRESP, HCLK, HRESETn
    );

    modport slave (
        input   HADDR, HBURST, HMASTLOCK, HPROT, HSIZE, HTRANS, HWDATA, HWRITE, HSEL, HCLK, HRESETn,
        output  HRDATA, HREADY, HRESP
    );
endinterface

`endif
