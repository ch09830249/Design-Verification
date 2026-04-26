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
    endfunction : build_phase

    virtual function void write ( ahb_seq_item txn );
        bit [`D_DATA_WIDTH-1:0] exp_data;
        int unsigned            byte_offset, half_offset;
        int unsigned            word_idx;

        // 統一計算 word index: byte address → word address
        word_idx = txn.HADDR >> $clog2(`D_DATA_WIDTH/8);

        // AHB TXN completes: HTRANS=NONSEQ or SEQ, HREADY=1, HRESP=OKAY
        if ( txn.HSEL && (txn.HTRANS inside {2'b10, 2'b11}) && txn.HREADY && !txn.HRESP ) begin
            if ( txn.HWRITE ) begin  // AHB write
                case ( txn.HSIZE )
                    `HSIZE_BYTE : begin
                        byte_offset = txn.HADDR[1:0] * 8;
                        mem[word_idx][byte_offset +: 8] = txn.HWDATA[byte_offset +: 8];
                    end
                    `HSIZE_HALFWORD : begin
                        half_offset = txn.HADDR[1] * 16;
                        mem[word_idx][half_offset +: 16] = txn.HWDATA[half_offset +: 16];
                    end
                    default : begin  // HSIZE_WORD
                        mem[word_idx] = txn.HWDATA;
                    end
                endcase
            end else begin          // AHB read
                exp_data = mem[word_idx];
                case ( txn.HSIZE )
                    `HSIZE_BYTE : begin
                        byte_offset = txn.HADDR[1:0] * 8;
                        exp_data = { '0, exp_data[byte_offset +: 8] };
                    end
                    `HSIZE_HALFWORD : begin
                        half_offset = txn.HADDR[1] * 16;
                        exp_data = { '0, exp_data[half_offset +: 16] };
                    end
                    default : ;  // HSIZE_WORD，直接用 exp_data
                endcase

                if ( exp_data !== txn.HRDATA ) begin
                    `uvm_fatal(
                        "DATA_MISMATCH",
                        $sformatf("Read addr=0x%h size=%0h: got=0x%h exp=0x%h",
                                  txn.HADDR, txn.HSIZE, txn.HRDATA, exp_data)
                    )
                end
                    `uvm_info(
                        "DATA_MATCH",
                        $sformatf("Read addr=0x%h size=%0h: data=0x%h OK",
                                  txn.HADDR, txn.HSIZE, txn.HRDATA),
                        UVM_LOW
                    )
            end
        end
    endfunction

endclass

`endif
