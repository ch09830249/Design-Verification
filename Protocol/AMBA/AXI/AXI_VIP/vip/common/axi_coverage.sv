`ifndef AXI_COVERAGE_SV
`define AXI_COVERAGE_SV

`include "axi_define.svh"

class axi_coverage extends uvm_subscriber #(axi_seq_item);
    `uvm_component_utils(axi_coverage)

    axi_seq_item        txn;

    covergroup axi_cg;
        option.per_instance = 1;

        cp_addr: coverpoint txn.addr {
            bins addr_bins[] = {[0:`D_MEM_SIZE-1]} with ( (item % (`D_DATA_WIDTH/8)) == 0 );
        }
        cp_op:      coverpoint txn.write;
        cp_id:      coverpoint txn.id    { bins id_bins[]  = {[0:(1<<`D_ID_WIDTH)-1]}; }
        cp_burst:   coverpoint txn.burst { bins burst_valid[] = {2'b00, 2'b01, 2'b10}; }  // FIXED, INCR, WRAP
        cp_size:    coverpoint txn.size  { bins size_valid[]  = {3'b000, 3'b001, 3'b010}; }  // BYTE, HALFWORD, WORD
        cp_len:     coverpoint txn.len   { bins len_single = {0};
                                           bins len_short  = {[1:3]};
                                           bins len_medium = {[4:15]};
                                           bins len_max    = {[16:255]}; }
        cp_bresp:   coverpoint txn.bresp { bins okay   = {2'b00};
                                           bins slverr = {2'b10}; }
        cp_rresp:   coverpoint txn.rresp[0] { bins okay   = {2'b00};
                                              bins slverr = {2'b10}; }

        addr_X_op:      cross cp_addr, cp_op;
        op_X_burst:     cross cp_op, cp_burst;
        op_X_size:      cross cp_op, cp_size;
        op_X_len:       cross cp_op, cp_len;
        id_X_op:        cross cp_id, cp_op;
    endgroup

    function new(string name = "axi_coverage", uvm_component parent);
        super.new(name, parent);
        axi_cg = new();
    endfunction

    virtual function void write(axi_seq_item t);
        txn = t;
        axi_cg.sample();
    endfunction

endclass

`endif
