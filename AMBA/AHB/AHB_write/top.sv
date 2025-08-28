module top;

  logic PCLK;
  logic PRESETn;

  apb_if apb_if_inst(.PCLK(PCLK), .PRESETn(PRESETn));

  // Clock generator
  initial begin
    PCLK = 0;
    forever #5 PCLK = ~PCLK;
  end

  // Reset generator
  initial begin
    PRESETn = 0;
    #20;
    PRESETn = 1;
  end

  apb_write_slave dut (
    .PCLK   (PCLK),
    .PRESETn(PRESETn),
    .PSEL   (apb_if_inst.PSEL),
    .PENABLE(apb_if_inst.PENABLE),
    .PWRITE (apb_if_inst.PWRITE),
    .PADDR  (apb_if_inst.PADDR),
    .PWDATA (apb_if_inst.PWDATA),
    .PREADY (apb_if_inst.PREADY)
  );

  initial begin
    run_test("apb_test");
  end

endmodule
