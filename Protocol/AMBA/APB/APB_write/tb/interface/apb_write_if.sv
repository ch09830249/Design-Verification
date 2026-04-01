interface apb_write_if(input logic PCLK, input logic PRESETn);

  logic [31:0] PADDR;
  logic        PWRITE;
  logic        PENABLE;
  logic        PSEL;
  logic [31:0] PWDATA;
  logic        PREADY;

endinterface
