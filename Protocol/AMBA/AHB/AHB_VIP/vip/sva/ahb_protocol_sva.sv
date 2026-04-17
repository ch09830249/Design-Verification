`ifndef AHB_PROTOCOL_SVA_SV
`define AHB_PROTOCOL_SVA_SV

`include "ahb_define.svh"

module ahb_protocol_sva (
    input   logic                           HCLK,
    input   logic                           HRESETn,
    input   logic [`D_ADDR_WIDTH-1:0]       HADDR,
    input   logic                           HWRITE,
    input   logic [`D_SLV_COUNT-1:0]        HSEL,
    input   logic [1:0]                     HTRANS,
    input   logic [2:0]                     HBURST,
    input   logic [2:0]                     HSIZE,
    input   logic [`D_DATA_WIDTH-1:0]       HWDATA,
    input   logic                           HMASTLOCK,
    input   logic [`D_DATA_WIDTH-1:0]       HRDATA,
    input   logic                           HREADY,
    input   logic                           HRESP
);

    wire ahb_active = HSEL && (HTRANS inside {`HTRANS_NONSEQ, `HTRANS_SEQ});

    // -------------------------------------------------------
    // Reset
    // -------------------------------------------------------
    property p_reset_hsel;
        @(posedge HCLK)
        (!HRESETn && !$isunknown(HSEL)) |-> (HSEL == '0);
    endproperty
    ahb_reset_hsel_rule: assert property(p_reset_hsel);

    property p_reset_htrans;
        @(posedge HCLK)
        (!HRESETn && !$isunknown(HTRANS)) |-> (HTRANS == `HTRANS_IDLE);
    endproperty
    ahb_reset_htrans_rule: assert property(p_reset_htrans);

    // -------------------------------------------------------
    // Idle Phase
    // -------------------------------------------------------
    property p_idle_phase;
        @(posedge HCLK) disable iff (!HRESETn)
        (HSEL == '0) |-> (HTRANS == `HTRANS_IDLE);
    endproperty
    ahb_idle_phase_rule: assert property(p_idle_phase);

    // -------------------------------------------------------
    // Address Phase — Signal Validity
    // -------------------------------------------------------
    property p_htrans_valid;
        @(posedge HCLK) disable iff (!HRESETn)
        HSEL |-> !$isunknown(HTRANS);
    endproperty
    ahb_htrans_valid_rule: assert property(p_htrans_valid);

    property p_hsize_valid;
        @(posedge HCLK) disable iff (!HRESETn)
        ahb_active |-> (HSIZE inside {`HSIZE_BYTE, `HSIZE_HALFWORD, `HSIZE_WORD});
    endproperty
    ahb_hsize_valid_rule: assert property(p_hsize_valid);

    property p_addr_aligned;
        @(posedge HCLK) disable iff (!HRESETn)
        ahb_active |-> (HADDR % (1 << HSIZE) == 0);
    endproperty
    ahb_addr_aligned_rule: assert property(p_addr_aligned);

    // -------------------------------------------------------
    // Data Phase — Signal Stability (during wait states)
    // -------------------------------------------------------
    property p_haddr_stable;
        @(posedge HCLK) disable iff (!HRESETn)
        (ahb_active && !HREADY) |-> $stable(HADDR);
    endproperty
    ahb_haddr_stable_rule: assert property(p_haddr_stable);

    property p_hwrite_stable;
        @(posedge HCLK) disable iff (!HRESETn)
        (ahb_active && !HREADY) |-> $stable(HWRITE);
    endproperty
    ahb_hwrite_stable_rule: assert property(p_hwrite_stable);

    property p_htrans_stable;
        @(posedge HCLK) disable iff (!HRESETn)
        (ahb_active && !HREADY) |-> $stable(HTRANS);
    endproperty
    ahb_htrans_stable_rule: assert property(p_htrans_stable);

    property p_hwdata_stable;
        @(posedge HCLK) disable iff (!HRESETn)
        (ahb_active && HWRITE && !HREADY) |-> $stable(HWDATA);
    endproperty
    ahb_hwdata_stable_rule: assert property(p_hwdata_stable);

    // -------------------------------------------------------
    // Handshake
    // -------------------------------------------------------
    property p_hready_eventually;
        @(posedge HCLK) disable iff (!HRESETn)
        $rose(ahb_active) |-> ##[0:16] HREADY;
    endproperty
    ahb_hready_eventually_rule: assert property(p_hready_eventually);

    // Transfer 完成後，下一拍不能是 SEQ（除非還在 burst）
    property p_transfer_done;
        @(posedge HCLK) disable iff (!HRESETn)
        (HSEL && HREADY && HTRANS == `HTRANS_IDLE) |=> (HTRANS == `HTRANS_IDLE || HTRANS == `HTRANS_NONSEQ);
    endproperty
    ahb_transfer_done_rule: assert property(p_transfer_done);

    // SEQ 之前必須有 NONSEQ 或 SEQ
    property p_seq_after_nonseq;
        @(posedge HCLK) disable iff (!HRESETn)
        (HSEL && HTRANS == `HTRANS_SEQ) |->
            $past(HTRANS == `HTRANS_NONSEQ || HTRANS == `HTRANS_SEQ);
    endproperty
    ahb_seq_after_nonseq_rule: assert property(p_seq_after_nonseq);

    // -------------------------------------------------------
    // Error Response
    // -------------------------------------------------------
    property p_hresp_two_cycle;
        @(posedge HCLK) disable iff (!HRESETn)
        (HRESP && !HREADY) |=> (HRESP && HREADY);
    endproperty
    ahb_hresp_two_cycle_rule: assert property(p_hresp_two_cycle);

    property p_hresp_in_active;
        @(posedge HCLK) disable iff (!HRESETn)
        HRESP |-> ahb_active;
    endproperty
    ahb_hresp_in_active_rule: assert property(p_hresp_in_active);

endmodule

`endif
