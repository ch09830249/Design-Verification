module d_slave (input  clk,
                        reset,
                        enable,
                        // Many more input signals...     很多 Signals 要連接
                output gnt,
                       irq,
                        // Many more output signals...);
    // Some design functionality
    endmodule

module d_top ( [top_level_ports] );
    reg [`NUM_SLAVES-1:0] clk;                  // Assume `NUM_SLAVES is a macro set to 2
    reg [`NUM_SLAVES-1:0] tb_reset;
    // Other declarations

	d_slave slave_0  (  .clk   (d_clk[0]),      // These connections have to be     例化一個 module 時, 連接 signal 很麻煩, 不會 interface 可以直接連
	                  	.reset (d_reset[0]) 	  // repeated for all other slave instances
	                  		...
	                  	.gnt (d_gnt[0]),
	                  	... );

	d_slave slave_1  ( ... );
	d_slave slave_2  ( ... );
endmodule