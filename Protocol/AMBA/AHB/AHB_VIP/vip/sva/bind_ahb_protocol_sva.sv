`ifndef BIND_AHB_PROTOCOL_SVA_SV
`define BIND_AHB_PROTOCOL_SVA_SV

bind sim_top ahb_protocol_sva bind_ahb_sva (
    .HCLK(vif.HCLK),
    .HRESETn(vif.HRESETn),
    .HADDR(vif.HADDR),
    .HWRITE(vif.HWRITE),
    .HSEL(vif.HSEL),
    .HTRANS(vif.HTRANS),
    .HBURST(vif.HBURST),
    .HSIZE(vif.HSIZE),
    .HWDATA(vif.HWDATA),
    .HMASTLOCK(vif.HMASTLOCK),
    .HRDATA(vif.HRDATA),
    .HREADY(vif.HREADY),
    .HRESP(vif.HRESP)
);

`endif
