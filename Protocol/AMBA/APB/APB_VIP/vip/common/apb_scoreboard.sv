`ifndef APB_SCOREBOARD_SV
`define APB_SCOREBOARD_SV

`include "apb_define.svh"

class apb_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(apb_scoreboard)

    logic [`D_DATA_WIDTH-1:0]                           mem [`D_MEM_SIZE-1:0];

    uvm_analysis_imp #(apb_seq_item, apb_scoreboard)    imp;
    
    function new ( string name = "apb_scoreboard", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );
        super.build_phase(phase);
        imp = new("imp", this);
        foreach ( mem[i] ) mem[i] = 0;
    endfunction: build_phase

    virtual function void write ( apb_seq_item txn );
        bit [`D_DATA_WIDTH-1:0]     exp_data;

        if ( txn.PSEL && txn.PENABLE && txn.PREADY ) begin  // TXN completes
            if ( txn.PWRITE && !txn.PSLVERR ) begin  // APB write
                mem[txn.PADDR[$clog2(`D_MEM_SIZE)-1:0]] = txn.PWDATA;
            end else begin  // APB read
                exp_data = mem[txn.PADDR[$clog2(`D_MEM_SIZE)-1:0]];
                if ( exp_data != txn.PRDATA ) begin
                    `uvm_error(
                        "MISCOMPARE",
                        $sformatf("Read addr (0x%h): data = 0x%h while expected 0x%h",txn.PADDR, txn.PRDATA, exp_data)
                    )
                end
            end
        end
    endfunction
endclass

`endif
