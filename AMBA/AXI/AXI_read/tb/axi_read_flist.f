module top;

  logic HCLK;
  logic HRESETn;

  // Instantiate interface
  ahb_if ahb_if_inst(.HCLK(HCLK), .HRESETn(HRESETn));

  // Clock generation
  initial begin
    HCLK = 0;
    forever #5 HCLK = ~HCLK;
  end

  // Reset generation
  initial begin
    HRESETn = 0;
    #20 HRESETn = 1;
  end

  // DUT instance
  ahb_write_slavel dut (
    .HCLK      (HCLK),
    .HRESETn   (HRESETn),
    .HSEL      (ahb_if_inst.HSEL),
    .HWRITE    (ahb_if_inst.HWRITE),
    .HTRANS    (ahb_if_inst.HTRANS),
    .HADDR     (ahb_if_inst.HADDR),
    .HWDATA    (ahb_if_inst.HWDATA),
    .HREADYOUT (ahb_if_inst.HREADYOUT)
  );

  // Connect VIP to interface
  initial begin
    uvm_config_db#(virtual ahb_if)::set(null, "*", "vif", ahb_if_inst);
  end

  initial begin
    run_test("ahb_test");
  end

endmodule
