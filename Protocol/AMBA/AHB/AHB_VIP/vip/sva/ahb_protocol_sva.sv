`ifndef APB_PROTOCOL_SVA_SV
`define APB_PROTOCOL_SVA_SV

`include "apb_define.svh"

module ahb_protocol_sva (
    input   logic                           PCLK,
    input   logic                           PRESETn,
    input   logic [`D_ADDR_WIDTH-1:0]       PADDR,
    input   logic                           PWRITE,
    input   logic [`D_SLV_COUNT-1:0]        PSEL,
    input   logic                           PENABLE,
    input   logic [`D_DATA_WIDTH-1:0]       PWDATA,

    // Slave Signal
    input   logic                           PREADY,
    input   logic [`D_DATA_WIDTH-1:0]       PRDATA,
    input   logic                           PSLVERR
    
);
    // -------------------------------------------------------
    // Reset
    // -------------------------------------------------------
    property p_reset_psel;
        @(posedge PCLK)
        (!PRESETn && !$isunknown(PSEL)) |-> (PSEL == '0);
    endproperty
    apb_reset_psel_rule: assert property(p_reset_psel);

    property p_reset_penable;
        @(posedge PCLK)
        (!PRESETn && !$isunknown(PENABLE)) |-> !PENABLE;
    endproperty
    apb_reset_penable_rule: assert property(p_reset_penable);

    // -------------------------------------------------------
    // Idle Phase
    // -------------------------------------------------------
    property p_idle_phase;
        @(posedge PCLK) disable iff (!PRESETn)
        (PSEL == '0) |-> !PENABLE;
    endproperty
    apb_idle_phase_rule: assert property(p_idle_phase);

    // -------------------------------------------------------
    // Setup Phase
    // -------------------------------------------------------
    property p_setup_phase_penable_low;
        @(posedge PCLK) disable iff (!PRESETn)
        ((PSEL == '0) ##1 (PSEL != '0)) |-> !PENABLE;
    endproperty
    apb_setup_phase_penable_low_rule: assert property(p_setup_phase_penable_low);

    property p_psel_to_penable;
        @(posedge PCLK) disable iff (!PRESETn)
        ((PSEL == '0) ##1 (PSEL != '0)) |=> (PSEL != '0 && PENABLE);
    endproperty
    apb_psel_to_penable_rule: assert property(p_psel_to_penable);

    // -------------------------------------------------------
    // Access Phase — Signal Stability
    // -------------------------------------------------------
    property p_paddr_stable;
        @(posedge PCLK) disable iff (!PRESETn)
        (PSEL && PENABLE && !$rose(PENABLE) && !PREADY) |-> $stable(PADDR);
    endproperty
    apb_paddr_stable_rule: assert property(p_paddr_stable);

    property p_pwrite_stable;
        @(posedge PCLK) disable iff (!PRESETn)
        (PSEL && PENABLE && !$rose(PENABLE) && !PREADY) |-> $stable(PWRITE);
    endproperty
    apb_pwrite_stable_rule: assert property(p_pwrite_stable);

    property p_pwdata_stable;
        @(posedge PCLK) disable iff (!PRESETn)
        (PSEL && PENABLE && PWRITE && !$rose(PENABLE) && !PREADY) |-> $stable(PWDATA);
    endproperty
    apb_pwdata_stable_rule: assert property(p_pwdata_stable);

    // -------------------------------------------------------
    // Access Phase — Handshake
    // -------------------------------------------------------
    property p_pready_eventually;
        @(posedge PCLK) disable iff (!PRESETn)
        $rose(PENABLE) |-> ##[0:16] PREADY;
    endproperty
    apb_pready_eventually_rule: assert property(p_pready_eventually);

    property p_transfer_done;
        @(posedge PCLK) disable iff (!PRESETn)
        (PSEL && PENABLE && PREADY) |=> !PENABLE;
    endproperty
    apb_transfer_done_rule: assert property(p_transfer_done);

    property p_pslverr_with_pready;
        @(posedge PCLK) disable iff (!PRESETn)
        PSLVERR |-> PREADY;
    endproperty
    apb_pslverr_with_pready_rule: assert property(p_pslverr_with_pready);

    property p_pslverr_in_access;
        @(posedge PCLK) disable iff (!PRESETn)
        PSLVERR |-> (PSEL && PENABLE);
    endproperty
    apb_pslverr_in_access_rule: assert property(p_pslverr_in_access);

endmodule

`endif
