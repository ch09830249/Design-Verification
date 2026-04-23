`ifndef AHB_SEQ_ITEM_SV
`define AHB_SEQ_ITEM_SV

`include "ahb_define.svh"

class ahb_seq_item extends uvm_sequence_item;

    rand bit [`D_ADDR_WIDTH-1:0]    HADDR;
    rand bit                        HWRITE;
    rand bit [`D_DATA_WIDTH-1:0]    HWDATA;
    rand bit [2:0]                  HBURST;
    rand bit [2:0]                  HSIZE;
    rand int unsigned               burst_len;

    bit [`D_DATA_WIDTH-1:0]         HRDATA;
    bit                             HREADY;
    bit                             HRESP;
    bit [1:0]                       HTRANS    = `HTRANS_NONSEQ;
    bit [3:0]                       HPROT     = 4'b0011;    // Data/Privileged access
    bit                             HMASTLOCK = 0;
    bit [`D_SLV_COUNT-1:0]          HSEL      = 1;

    `uvm_object_utils_begin(ahb_seq_item)
        `uvm_field_int(HADDR,     UVM_ALL_ON)
        `uvm_field_int(HWRITE,    UVM_ALL_ON)
        `uvm_field_int(HSEL,      UVM_ALL_ON)
        `uvm_field_int(HWDATA,    UVM_ALL_ON)
        `uvm_field_int(HBURST,    UVM_ALL_ON)
        `uvm_field_int(HSIZE,     UVM_ALL_ON)
        `uvm_field_int(HTRANS,    UVM_ALL_ON)
        `uvm_field_int(HPROT,     UVM_ALL_ON)
        `uvm_field_int(HMASTLOCK, UVM_ALL_ON)
        `uvm_field_int(burst_len, UVM_ALL_ON)
        `uvm_field_int(HRDATA,    UVM_ALL_ON)
        `uvm_field_int(HREADY, UVM_ALL_ON)
        `uvm_field_int(HRESP,     UVM_ALL_ON)
    `uvm_object_utils_end

    constraint hsize_valid_c     { HSIZE  inside {`HSIZE_BYTE, `HSIZE_HALFWORD, `HSIZE_WORD}; }
    constraint hburst_valid_c    { HBURST inside {`HBURST_SINGLE, `HBURST_INCR}; }
    constraint hsel_onehot_c     { $onehot(HSEL); }
    constraint addr_overflow_c   { HADDR + (burst_len * (1 << HSIZE)) <= `D_MEM_SIZE; }
    constraint align_addr_c      { HADDR % (1 << HSIZE) == 0; }
    constraint burst_len_valid_c { burst_len inside {[1:16]}; }
    constraint single_len_c      { ( HBURST == `HBURST_SINGLE ) -> ( burst_len == 1 ); }

    function new ( string name = "ahb_seq_item" );
        super.new(name);
    endfunction

endclass

`endif
