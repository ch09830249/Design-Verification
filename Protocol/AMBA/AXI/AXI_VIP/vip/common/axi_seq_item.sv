`ifndef AXI_SEQ_ITEM_SV
`define AXI_SEQ_ITEM_SV

`include "axi_define.svh"

class axi_seq_item extends uvm_sequence_item;

    // ---- Address channels (AW / AR) ----
    rand bit [`D_ADDR_WIDTH-1:0]    addr;
    rand bit                        write;      // 1=write, 0=read
    rand bit [`D_ID_WIDTH-1:0]      id;
    rand bit [7:0]                  len;        // beats - 1 (AWLEN / ARLEN)
    rand bit [2:0]                  size;       // AWSIZE / ARSIZE
    rand bit [1:0]                  burst;      // AWBURST / ARBURST

    // ---- Write data channel (W) ----
    rand bit [`D_DATA_WIDTH-1:0]    wdata [];   // dynamic, size = len+1
    rand bit [`D_DATA_WIDTH/8-1:0]  wstrb [];   // dynamic, size = len+1

    // ---- Response channels (B / R) - filled by monitor ----
    bit [`D_DATA_WIDTH-1:0]         rdata [];   // dynamic, size = len+1
    bit [1:0]                       rresp [];   // dynamic, size = len+1
    bit [1:0]                       bresp;

    `uvm_object_utils_begin(axi_seq_item)
        `uvm_field_int        (addr,  UVM_ALL_ON)
        `uvm_field_int        (write, UVM_ALL_ON)
        `uvm_field_int        (id,    UVM_ALL_ON)
        `uvm_field_int        (len,   UVM_ALL_ON)
        `uvm_field_int        (size,  UVM_ALL_ON)
        `uvm_field_int        (burst, UVM_ALL_ON)
        `uvm_field_sarray_int (wdata, UVM_ALL_ON)
        `uvm_field_sarray_int (wstrb, UVM_ALL_ON)
        `uvm_field_sarray_int (rdata, UVM_ALL_ON)
        `uvm_field_sarray_int (rresp, UVM_ALL_ON)
        `uvm_field_int        (bresp, UVM_ALL_ON)
    `uvm_object_utils_end

    constraint size_valid_c  { size  inside {`ASIZE_BYTE, `ASIZE_HALFWORD, `ASIZE_WORD}; }
    constraint burst_valid_c { burst inside {`ABURST_FIXED, `ABURST_INCR}; }  // Not support `ABURST_WRAP
    constraint len_valid_c   { len   inside {[0:15]}; }        // 1~16 beats
    constraint fixed_len_c   { (burst == `ABURST_FIXED) -> (len == 0); }
    constraint align_addr_c  { addr % (1 << size) == 0; }
    constraint overflow_c    { addr + ((len + 1) * (1 << size)) <= `D_MEM_SIZE; }

    // wdata / wstrb 陣列大小與 len 對齊
    constraint wdata_size_c {
        write -> (wdata.size() == len + 1);
        write -> (wstrb.size() == len + 1);
        !write -> (wdata.size() == 0);
        !write -> (wstrb.size() == 0);
    }

    // 預設全 byte enable
    constraint wstrb_full_c  { foreach (wstrb[i]) wstrb[i] == '1; }

    function new(string name = "axi_seq_item");
        super.new(name);
    endfunction

endclass

`endif
