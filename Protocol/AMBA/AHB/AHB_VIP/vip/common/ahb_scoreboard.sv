`ifndef AHB_SCOREBOARD_SV
`define AHB_SCOREBOARD_SV

`include "ahb_define.svh"

class ahb_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(ahb_scoreboard)

    logic [`D_DATA_WIDTH-1:0]                           mem [`D_MEM_SIZE-1:0];

    uvm_analysis_imp #(ahb_seq_item, ahb_scoreboard)    imp;
    
    function new ( string name = "ahb_scoreboard", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );
        super.build_phase(phase);
        imp = new("imp", this);
        foreach ( mem[i] ) mem[i] = 0;
    endfunction: build_phase

    virtual function void write ( ahb_seq_item txn );
        bit [`D_DATA_WIDTH-1:0]     exp_data;

        // AHB TXN completes: HTRANS=NONSEQ or SEQ, HREADY=1, HRESP=OKAY
        if ( txn.HSEL && (txn.HTRANS inside {2'b10, 2'b11}) && txn.HREADY && !txn.HRESP ) begin
            if ( txn.HWRITE ) begin  // AHB write
                case ( txn.HSIZE )
                    `HSIZE_BYTE : begin
                        mem[txn.HADDR[$clog2(`D_MEM_SIZE)-1:0]] =
                            { mem[txn.HADDR[$clog2(`D_MEM_SIZE)-1:0]][`D_DATA_WIDTH-1:8],
                              txn.HWDATA[7:0] };
                    end
                    `HSIZE_HALFWORD : begin
                        mem[txn.HADDR[$clog2(`D_MEM_SIZE)-1:0]] =
                            { mem[txn.HADDR[$clog2(`D_MEM_SIZE)-1:0]][`D_DATA_WIDTH-1:16],
                              txn.HWDATA[15:0] };
                    end
                    default : begin  // HSIZE_WORD
                        mem[txn.HADDR[$clog2(`D_MEM_SIZE)-1:0]] = txn.HWDATA;
                    end
                endcase
            end else begin  // AHB read
                exp_data = mem[txn.HADDR[$clog2(`D_MEM_SIZE)-1:0]];
                case ( txn.HSIZE )
                    `HSIZE_BYTE     : exp_data = { '0, exp_data[7:0]  };
                    `HSIZE_HALFWORD : exp_data = { '0, exp_data[15:0] };
                    default         : exp_data = exp_data;  // HSIZE_WORD
                endcase
                if ( exp_data != txn.HRDATA ) begin
                    `uvm_fatal(
                        "DATA_MISMATCH",
                        $sformatf("Read addr (0x%h) size=%0h: data = 0x%h while expected 0x%h",
                                  txn.HADDR, txn.HSIZE, txn.HRDATA, exp_data)
                    )
                end 
                else begin
                    `uvm_info(
                        "DATA_MATCH",
                        $sformatf("Read addr (0x%h) size=%0h: data = 0x%h and expected 0x%h",
                                txn.HADDR, txn.HSIZE, txn.HRDATA, exp_data),
                        UVM_LOW
                    )
                end
            end
        end
    endfunction
endclass

`endif
