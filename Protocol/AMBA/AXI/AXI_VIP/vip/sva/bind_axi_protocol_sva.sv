`ifndef BIND_AXI_PROTOCOL_SVA_SV
`define BIND_AXI_PROTOCOL_SVA_SV

bind sim_top axi_protocol_sva bind_axi_sva (
    .ACLK       (vif.ACLK),
    .ARESETn    (vif.ARESETn),
    // AW
    .AWID       (vif.AWID),
    .AWADDR     (vif.AWADDR),
    .AWLEN      (vif.AWLEN),
    .AWSIZE     (vif.AWSIZE),
    .AWBURST    (vif.AWBURST),
    .AWVALID    (vif.AWVALID),
    .AWREADY    (vif.AWREADY),
    // W
    .WDATA      (vif.WDATA),
    .WSTRB      (vif.WSTRB),
    .WLAST      (vif.WLAST),
    .WVALID     (vif.WVALID),
    .WREADY     (vif.WREADY),
    // B
    .BID        (vif.BID),
    .BRESP      (vif.BRESP),
    .BVALID     (vif.BVALID),
    .BREADY     (vif.BREADY),
    // AR
    .ARID       (vif.ARID),
    .ARADDR     (vif.ARADDR),
    .ARLEN      (vif.ARLEN),
    .ARSIZE     (vif.ARSIZE),
    .ARBURST    (vif.ARBURST),
    .ARVALID    (vif.ARVALID),
    .ARREADY    (vif.ARREADY),
    // R
    .RID        (vif.RID),
    .RDATA      (vif.RDATA),
    .RRESP      (vif.RRESP),
    .RLAST      (vif.RLAST),
    .RVALID     (vif.RVALID),
    .RREADY     (vif.RREADY)
);

`endif
