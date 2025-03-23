// Define a class called "Packet" with a 32-bit variable to store address
// Initialize "addr" to 32'hfade_cafe in the new function, also called constructor
class Packet;
  bit [31:0] addr;

  function new ();
    addr = 32'hfade_cafe;
  endfunction
endclass

module tb;

  // Create a class handle called "pkt" and instantiate the class object
  initial begin
    // The class's constructor new() fn is called when the object is instantiated
    Packet pkt = new();

    // Display the class variable - Because constructor was called during
    // instantiation, this variable is expected to have 32'hfade_cafe;
    $display ("addr=0x%0h", pkt.addr);
  end
endmodule

/*
  addr=0xfadecafe
*/