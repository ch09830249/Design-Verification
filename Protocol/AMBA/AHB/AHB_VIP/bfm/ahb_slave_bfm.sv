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

    // 暫存 address phase 資訊
    logic [`D_ADDR_WIDTH-1:0]   addr_reg;
    logic                       write_reg;
    logic [2:0]                 size_reg;
    logic                       valid_reg;

    // 組合邏輯判斷是否為有效 address phase
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
            // Data Phase — 處理上一個 address phase
            // ----------------------------------------
            if ( valid_reg ) begin
                vif.HREADY <= 1;
                vif.HRESP  <= `HRESP_OKAY;

                if ( write_reg ) begin
                    case ( size_reg )
                        `HSIZE_BYTE : begin
                            mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]] <=
                                { mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]][`D_DATA_WIDTH-1:8],
                                  vif.HWDATA[7:0] };
                        end
                        `HSIZE_HALFWORD : begin
                            mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]] <=
                                { mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]][`D_DATA_WIDTH-1:16],
                                  vif.HWDATA[15:0] };
                        end
                        default : begin  // HSIZE_WORD
                            mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]] <= vif.HWDATA;
                        end
                    endcase
                end else begin
                    vif.HRDATA <= mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]];
                end
            end

            // ----------------------------------------
            // Address Phase — 採樣當前 address phase
            // ----------------------------------------
            addr_reg  <= vif.HADDR;
            write_reg <= vif.HWRITE;
            size_reg  <= vif.HSIZE;
            valid_reg <= valid;

        end
    end

endmodule

`endif
