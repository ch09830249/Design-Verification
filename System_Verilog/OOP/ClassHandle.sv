// Create a new class with a single member called
// count that stores integer values
class Packet;
	int count;
endclass

module tb;
  	// Create a "handle" for the class Packet that can point to an
  	// object of the class type Packet
  	// Note: This "handle" now points to NULL
	Packet pkt;				// 其實和 Java 的 reference 是一樣的概念

  	initial begin
      if (pkt == null)
        $display ("Packet handle 'pkt' is null");

      // Display the class member using the "handle"
      // Expect a run-time error because pkt is not an object
      // yet, and is still pointing to NULL. So pkt is not
      // aware that it should hold a member
      $display ("count = %0d", pkt.count);
  	end
endmodule

/*
	Packet handle 'pkt' is null
	Assertion failed: cobj, file ../../iverilog/vvp/vthread.cc, line 4938
*/