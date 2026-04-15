`ifndef BIND_AHB_PROTOCOL_SVA_SV
`define BIND_AHB_PROTOCOL_SVA_SV

bind sim_top ahb_protocol_sva bind_ahb_sva (
    .PCLK(vif.PCLK),
    .PRESETn(vif.PRESETn),
    .PADDR(vif.PADDR),
    .PWRITE(vif.PWRITE),
    .PSEL(vif.PSEL),
    .PENABLE(vif.PENABLE),
    .PWDATA(vif.PWDATA),
    .PREADY(vif.PREADY),
    .PRDATA(vif.PRDATA),
    .PSLVERR(vif.PSLVERR)
);

`endif
