/*
  Syntax:
    modport  [identifier]  (
      input  [port_list],
      output [port_list]
    );

  EX:
    interface 	myInterface;
      logic 	ack;
      logic 	gnt;
      logic 	sel;
      logic 	irq0;

      // ack and sel are inputs to the dut0, while gnt and irq0 are outputs
      modport  dut0 (
        input 	ack, sel,
        output 	gnt, irq0
      );

      // ack and sel are outputs from dut1, while gnt and irq0 are inputs
      modport  dut1 (
        input 	gnt, irq0,
        output 	ack, sel
      );
    endinterface
*/

// Example of named port bundle
module dut0  ( myinterface.dut0  _if);  // myinterface 中的 dut0
	...
endmodule

module dut1  ( myInterface.dut1 _if);
	...
endmodule

module tb;
	myInterface 	_if;
	dut0  d0 	( .* );   // 都用 _if ? 所以用 .*
	dut1 	d1 	( .* );
endmodule

// Example of connecting port bundle
module dut0  ( myinterface  _if);
	...
endmodule

module dut1  ( myInterface _if);
	...
endmodule

module tb;
	myInterface 	_if;
	dut0  d0 	( ._if (_if.dut0));   // _if 連接 _if.dut0
	dut1 	d1 	( ._if (_if.dut1));
endmodule

// Example of connecting to generic interface
module dut0  ( interface  _if);
	...
endmodule

module dut1  ( interface _if);
	...
endmodule

module tb;
	myInterface 	_if;
	dut0  d0 	( ._if (_if.dut0));
	dut1 	d1 	( ._if (_if.dut1));
endmodule

