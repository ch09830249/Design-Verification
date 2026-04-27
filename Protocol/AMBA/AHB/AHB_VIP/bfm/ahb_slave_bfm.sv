`ifndef AHB_SLAVE_BFM_SV
`define AHB_SLAVE_BFM_SV

`include "ahb_define.svh"

module ahb_slave_bfm
(
    input   logic       HCLK,
    input   logic       HRESETn,
    ahb_interface       vif
);

    logic [`D_DATA_WIDTH-1:0]   mem [`D_MEM_SIZE-1:0];
    logic [`D_ADDR_WIDTH-1:0]   addr_reg;
    logic                       write_reg;
    logic [2:0]                 size_reg;
    logic                       valid_reg;

    localparam BYTE_OFFSET_BITS = $clog2(`D_DATA_WIDTH/8);

    wire valid = vif.HSEL && vif.HREADY &&
               ( vif.HTRANS == `HTRANS_NONSEQ ||
                 vif.HTRANS == `HTRANS_SEQ    );

    initial begin
        foreach ( mem[i] ) mem[i] = 0;
    end

    always @ ( posedge HCLK or negedge HRESETn ) begin
        if ( !HRESETn ) begin
            vif.HREADY  <= 1;
            vif.HRESP   <= `HRESP_OKAY;
            vif.HRDATA  <= 0;
            valid_reg   <= 0;
            addr_reg    <= 0;
            write_reg   <= 0;
            size_reg    <= 0;
        end else begin

            // ----------------------------------------
            // Data Phase
            // ----------------------------------------
            if ( valid_reg ) begin
                vif.HREADY <= 1;
                vif.HRESP  <= `HRESP_OKAY;

                if ( write_reg ) begin
                    case ( size_reg )
                        `HSIZE_BYTE : begin
                            mem[addr_reg >> BYTE_OFFSET_BITS]
                                [addr_reg[1:0]*8 +: 8]        <= vif.HWDATA[addr_reg[1:0]*8 +: 8];
                        end
                        `HSIZE_HALFWORD : begin
                            mem[addr_reg >> BYTE_OFFSET_BITS]
                                [addr_reg[1]*16 +: 16]        <= vif.HWDATA[addr_reg[1]*16 +: 16];
                        end
                        default : begin  // HSIZE_WORD
                            mem[addr_reg >> BYTE_OFFSET_BITS] <= vif.HWDATA;
                        end
                    endcase
                end else begin  // Read => 這裡的 read data 是直到 data phase 才給, 和 slave driver 不一樣
                    case ( size_reg )
                        `HSIZE_BYTE    : vif.HRDATA <= { '0, mem[addr_reg >> BYTE_OFFSET_BITS][addr_reg[1:0]*8 +: 8] };
                        `HSIZE_HALFWORD: vif.HRDATA <= { '0, mem[addr_reg >> BYTE_OFFSET_BITS][addr_reg[1]*16 +: 16] };
                        default        : vif.HRDATA <= mem[addr_reg >> BYTE_OFFSET_BITS];
                    endcase
                end
            end

            // ----------------------------------------
            // Address Phase
            // ----------------------------------------
            addr_reg  <= vif.HADDR;
            write_reg <= vif.HWRITE;
            size_reg  <= vif.HSIZE;
            valid_reg <= valid;

        end
    end

endmodule

`endif
