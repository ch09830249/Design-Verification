`ifndef AHB_COVERAGE_SV
`define AHB_COVERAGE_SV

`include "ahb_define.svh"

class ahb_coverage extends uvm_subscriber #(ahb_seq_item);
    `uvm_component_utils(ahb_coverage)

    ahb_seq_item        txn;

    covergroup ahb_cg;
        option.per_instance = 1;

        cp_addr: coverpoint txn.HADDR {
            bins addr_bins[] = {[0:`D_MEM_SIZE-1]} with ( (item % (`D_DATA_WIDTH/8)) == 0 );
        }
        cp_op:      coverpoint  txn.HWRITE;
        cp_sel:     coverpoint  txn.HSEL   { bins sel_bins[] = {[1:`D_SLV_COUNT]}; }
        cp_trans:   coverpoint  txn.HTRANS { bins trans_valid[] = {2'b10, 2'b11}; }  // NONSEQ, SEQ
        cp_burst:   coverpoint  txn.HBURST;
        cp_size:    coverpoint  txn.HSIZE  { bins size_valid[] = {3'b000, 3'b001, 3'b010}; }  // BYTE, HALFWORD, WORD

        addr_X_op_X_sel:    cross cp_addr, cp_op, cp_sel;
        op_X_burst:         cross cp_op, cp_burst;
        op_X_size:          cross cp_op, cp_size;
    endgroup

    function new ( string name = "ahb_coverage", uvm_component parent );
        super.new(name, parent);
        ahb_cg = new();
    endfunction
    
    virtual function void write ( ahb_seq_item t );
        // Address Phase: HTRANS=NONSEQ or SEQ, HSEL=1
        if ( t.HSEL && (t.HTRANS inside {2'b10, 2'b11}) ) begin
            txn = t;
            ahb_cg.sample();
        end
    endfunction
endclass

`endif
