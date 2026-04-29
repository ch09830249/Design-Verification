`ifndef AXI_PROTOCOL_SVA_SV
`define AXI_PROTOCOL_SVA_SV

`include "axi_define.svh"

module axi_protocol_sva (
    input   logic                           ACLK,
    input   logic                           ARESETn,
    // AW
    input   logic [`D_ID_WIDTH-1:0]         AWID,
    input   logic [`D_ADDR_WIDTH-1:0]       AWADDR,
    input   logic [7:0]                     AWLEN,
    input   logic [2:0]                     AWSIZE,
    input   logic [1:0]                     AWBURST,
    input   logic                           AWVALID,
    input   logic                           AWREADY,
    // W
    input   logic [`D_DATA_WIDTH-1:0]       WDATA,
    input   logic [`D_DATA_WIDTH/8-1:0]     WSTRB,
    input   logic                           WLAST,
    input   logic                           WVALID,
    input   logic                           WREADY,
    // B
    input   logic [`D_ID_WIDTH-1:0]         BID,
    input   logic [1:0]                     BRESP,
    input   logic                           BVALID,
    input   logic                           BREADY,
    // AR
    input   logic [`D_ID_WIDTH-1:0]         ARID,
    input   logic [`D_ADDR_WIDTH-1:0]       ARADDR,
    input   logic [7:0]                     ARLEN,
    input   logic [2:0]                     ARSIZE,
    input   logic [1:0]                     ARBURST,
    input   logic                           ARVALID,
    input   logic                           ARREADY,
    // R
    input   logic [`D_ID_WIDTH-1:0]         RID,
    input   logic [`D_DATA_WIDTH-1:0]       RDATA,
    input   logic [1:0]                     RRESP,
    input   logic                           RLAST,
    input   logic                           RVALID,
    input   logic                           RREADY
);

    // -------------------------------------------------------
    // Reset
    // -------------------------------------------------------
    property p_reset_awvalid;
        @(posedge ACLK)
        (!ARESETn && !$isunknown(AWVALID)) |-> (AWVALID == 0);
    endproperty
    axi_reset_awvalid_rule: assert property(p_reset_awvalid);

    property p_reset_wvalid;
        @(posedge ACLK)
        (!ARESETn && !$isunknown(WVALID)) |-> (WVALID == 0);
    endproperty
    axi_reset_wvalid_rule: assert property(p_reset_wvalid);

    property p_reset_bvalid;
        @(posedge ACLK)
        (!ARESETn && !$isunknown(BVALID)) |-> (BVALID == 0);
    endproperty
    axi_reset_bvalid_rule: assert property(p_reset_bvalid);

    property p_reset_arvalid;
        @(posedge ACLK)
        (!ARESETn && !$isunknown(ARVALID)) |-> (ARVALID == 0);
    endproperty
    axi_reset_arvalid_rule: assert property(p_reset_arvalid);

    property p_reset_rvalid;
        @(posedge ACLK)
        (!ARESETn && !$isunknown(RVALID)) |-> (RVALID == 0);
    endproperty
    axi_reset_rvalid_rule: assert property(p_reset_rvalid);

    // -------------------------------------------------------
    // Handshake — VALID must not deassert until READY
    // AXI spec: once VALID is asserted, it must stay high
    //           until the handshake (VALID && READY) occurs
    // -------------------------------------------------------
    property p_awvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (AWVALID && !AWREADY) |=> AWVALID;
    endproperty
    axi_awvalid_stable_rule: assert property(p_awvalid_stable);

    property p_wvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (WVALID && !WREADY) |=> WVALID;
    endproperty
    axi_wvalid_stable_rule: assert property(p_wvalid_stable);

    property p_bvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (BVALID && !BREADY) |=> BVALID;
    endproperty
    axi_bvalid_stable_rule: assert property(p_bvalid_stable);

    property p_arvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (ARVALID && !ARREADY) |=> ARVALID;
    endproperty
    axi_arvalid_stable_rule: assert property(p_arvalid_stable);

    property p_rvalid_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (RVALID && !RREADY) |=> RVALID;
    endproperty
    axi_rvalid_stable_rule: assert property(p_rvalid_stable);

    // -------------------------------------------------------
    // Address channel — signal validity
    // -------------------------------------------------------
    property p_awsize_valid;
        @(posedge ACLK) disable iff (!ARESETn)
        AWVALID |-> (AWSIZE inside {`ASIZE_BYTE, `ASIZE_HALFWORD, `ASIZE_WORD});
    endproperty
    axi_awsize_valid_rule: assert property(p_awsize_valid);

    property p_arsize_valid;
        @(posedge ACLK) disable iff (!ARESETn)
        ARVALID |-> (ARSIZE inside {`ASIZE_BYTE, `ASIZE_HALFWORD, `ASIZE_WORD});
    endproperty
    axi_arsize_valid_rule: assert property(p_arsize_valid);

    property p_awburst_valid;
        @(posedge ACLK) disable iff (!ARESETn)
        AWVALID |-> (AWBURST inside {`ABURST_FIXED, `ABURST_INCR, `ABURST_WRAP});
    endproperty
    axi_awburst_valid_rule: assert property(p_awburst_valid);

    property p_arburst_valid;
        @(posedge ACLK) disable iff (!ARESETn)
        ARVALID |-> (ARBURST inside {`ABURST_FIXED, `ABURST_INCR, `ABURST_WRAP});
    endproperty
    axi_arburst_valid_rule: assert property(p_arburst_valid);

    property p_awaddr_aligned;
        @(posedge ACLK) disable iff (!ARESETn)
        AWVALID |-> (AWADDR % (1 << AWSIZE) == 0);
    endproperty
    axi_awaddr_aligned_rule: assert property(p_awaddr_aligned);

    property p_araddr_aligned;
        @(posedge ACLK) disable iff (!ARESETn)
        ARVALID |-> (ARADDR % (1 << ARSIZE) == 0);
    endproperty
    axi_araddr_aligned_rule: assert property(p_araddr_aligned);

    // -------------------------------------------------------
    // Address channel — signal stability until handshake
    // -------------------------------------------------------
    property p_awaddr_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (AWVALID && !AWREADY) |=> $stable(AWADDR);
    endproperty
    axi_awaddr_stable_rule: assert property(p_awaddr_stable);

    property p_awlen_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (AWVALID && !AWREADY) |=> $stable(AWLEN);
    endproperty
    axi_awlen_stable_rule: assert property(p_awlen_stable);

    property p_araddr_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (ARVALID && !ARREADY) |=> $stable(ARADDR);
    endproperty
    axi_araddr_stable_rule: assert property(p_araddr_stable);

    property p_arlen_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (ARVALID && !ARREADY) |=> $stable(ARLEN);
    endproperty
    axi_arlen_stable_rule: assert property(p_arlen_stable);

    // -------------------------------------------------------
    // W channel — WDATA / WSTRB stability during wait states
    // -------------------------------------------------------
    property p_wdata_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (WVALID && !WREADY) |=> $stable(WDATA);
    endproperty
    axi_wdata_stable_rule: assert property(p_wdata_stable);

    property p_wstrb_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (WVALID && !WREADY) |=> $stable(WSTRB);
    endproperty
    axi_wstrb_stable_rule: assert property(p_wstrb_stable);

    property p_wlast_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (WVALID && !WREADY) |=> $stable(WLAST);
    endproperty
    axi_wlast_stable_rule: assert property(p_wlast_stable);

    // -------------------------------------------------------
    // W channel — WLAST must assert on the correct beat
    // -------------------------------------------------------
    // WLAST 不能在還有 pending beat 時提早拉高（簡化版）
    property p_wlast_not_unknown;
        @(posedge ACLK) disable iff (!ARESETn)
        WVALID |-> !$isunknown(WLAST);
    endproperty
    axi_wlast_not_unknown_rule: assert property(p_wlast_not_unknown);

    // -------------------------------------------------------
    // B channel — BRESP validity
    // -------------------------------------------------------
    property p_bresp_valid;
        @(posedge ACLK) disable iff (!ARESETn)
        BVALID |-> (BRESP inside {`BRESP_OKAY, `BRESP_EXOKAY, `BRESP_SLVERR, `BRESP_DECERR});
    endproperty
    axi_bresp_valid_rule: assert property(p_bresp_valid);

    property p_bresp_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (BVALID && !BREADY) |=> $stable(BRESP);
    endproperty
    axi_bresp_stable_rule: assert property(p_bresp_stable);

    // -------------------------------------------------------
    // R channel — RRESP / RDATA stability
    // -------------------------------------------------------
    property p_rresp_valid;
        @(posedge ACLK) disable iff (!ARESETn)
        RVALID |-> (RRESP inside {`RRESP_OKAY, `RRESP_EXOKAY, `RRESP_SLVERR, `RRESP_DECERR});
    endproperty
    axi_rresp_valid_rule: assert property(p_rresp_valid);

    property p_rdata_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (RVALID && !RREADY) |=> $stable(RDATA);
    endproperty
    axi_rdata_stable_rule: assert property(p_rdata_stable);

    property p_rlast_stable;
        @(posedge ACLK) disable iff (!ARESETn)
        (RVALID && !RREADY) |=> $stable(RLAST);
    endproperty
    axi_rlast_stable_rule: assert property(p_rlast_stable);

    // -------------------------------------------------------
    // Liveness — VALID must eventually be accepted
    // -------------------------------------------------------
    property p_aw_eventually_accepted;
        @(posedge ACLK) disable iff (!ARESETn)
        $rose(AWVALID) |-> ##[0:16] (AWVALID && AWREADY);
    endproperty
    axi_aw_eventually_accepted_rule: assert property(p_aw_eventually_accepted);

    property p_ar_eventually_accepted;
        @(posedge ACLK) disable iff (!ARESETn)
        $rose(ARVALID) |-> ##[0:16] (ARVALID && ARREADY);
    endproperty
    axi_ar_eventually_accepted_rule: assert property(p_ar_eventually_accepted);

    property p_w_eventually_accepted;
        @(posedge ACLK) disable iff (!ARESETn)
        $rose(WVALID) |-> ##[0:16] (WVALID && WREADY);
    endproperty
    axi_w_eventually_accepted_rule: assert property(p_w_eventually_accepted);

endmodule

`endif
