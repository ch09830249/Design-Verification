interface apb_read_if(input logic PCLK, input logic PRESETn);

  logic        PSEL;
  logic        PENABLE;
  logic        PWRITE;
  logic [31:0] PADDR;
  logic [31:0] PRDATA;
  logic        PREADY;

endinterface
