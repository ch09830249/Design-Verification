`ifndef AGT_COVERAGE_SV
`define AGT_COVERAGE_SV

`include "apb_define.svh"

class ahb_coverage extends uvm_subscriber #(apb_seq_item);
    `uvm_component_utils(apb_coverage)

    apb_seq_item        txn;

    covergroup apb_cg;
        option.per_instance = 1;

        cp_addr: coverpoint txn.PADDR {
            bins addr_bins[] = {[0:`D_MEM_SIZE-1]} with ( (item % (`D_DATA_WIDTH/8)) == 0 );
        }
        cp_op:      coverpoint  txn.PWRITE;
        cp_sel:     coverpoint  txn.PSEL { bins sel_bins[] = {[1:`D_SLV_COUNT]}; }

        addr_X_op_X_sel:    cross cp_addr, cp_op, cp_sel;
    endgroup

    function new ( string name = "apb_coverage", uvm_component parent );
        super.new(name, parent);
        apb_cg = new();
    endfunction
    
    virtual function void write ( apb_seq_item t );
        if ( t.PSEL && t.PENABLE ) begin  // Access Phase
            txn = t;
            apb_cg.sample();
        end
    endfunction
endclass

`endif
