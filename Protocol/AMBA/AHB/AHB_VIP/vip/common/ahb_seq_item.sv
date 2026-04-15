`ifndef APB_SEQ_ITEM_SV
`define APB_SEQ_ITEM_SV

`include "ahb_define.svh"

class ahb_seq_item extends uvm_sequence_item;
    
    rand bit [`D_ADDR_WIDTH-1:0]    PADDR;
    rand bit                        PWRITE;
    rand bit [`D_SLV_COUNT-1:0]     PSEL;
    rand bit [`D_DATA_WIDTH-1:0]    PWDATA;

    bit                             PENABLE;
    bit                             PREADY;
    bit [`D_DATA_WIDTH-1:0]         PRDATA;
    bit                             PSLVERR;

    `uvm_object_utils_begin(apb_seq_item)
        `uvm_field_int(PADDR, UVM_ALL_ON)
        `uvm_field_int(PWRITE, UVM_ALL_ON)
        `uvm_field_int(PSEL, UVM_ALL_ON)
        `uvm_field_int(PWDATA, UVM_ALL_ON)
        `uvm_field_int(PENABLE, UVM_ALL_ON)
        `uvm_field_int(PREADY, UVM_ALL_ON)
        `uvm_field_int(PRDATA, UVM_ALL_ON)
        `uvm_field_int(PSLVERR, UVM_ALL_ON)
    `uvm_object_utils_end

    constraint psel_onehot_c { $onehot(PSEL); }
    constraint addr_overflow_c { PADDR < `D_MEM_SIZE; }
    constraint align_addr_to_width_c { PADDR % (`D_DATA_WIDTH / 8) == 0; }

    function new ( string name = "apb_seq_item" );
        super.new(name);
    endfunction

endclass

`endif
