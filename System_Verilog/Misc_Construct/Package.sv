package my_pkg;

    // Create typedef declarations that can be reused in multiple modules
	typedef enum bit [1:0] { RED, YELLOW, GREEN, RSVD } e_signal;

	typedef struct { bit [3:0]   signal_id;
                     bit         active;
                     bit [1:0]   timeout;
                   } e_sig_param;

    // Create function and task defintions that can be reused
    // Note that it will be a 'static' method if the keyword 'automatic' is not used
	function int calc_parity ();
      $display ("Called from somewhere");
   	endfunction

endpackage

/*
    import <package_name>::*; // Imports all items
    import <package_name>::<item_name>; // Imports specific item

    When package items are imported using a wildcard, only the items that are actually utilized in the module or interface are imported. 其實只會 import 會用到的
    Any definitions and declarations in the package that are not referenced remain unimported. So, an import essentially means that it is made visible.
*/

// Import the package defined above to use e_signal
import my_pkg::*;

class myClass;
	e_signal 	m_signal;
endclass

module tb;
	myClass cls;

	initial begin
		cls          = new();
		cls.m_signal = GREEN;
		$display ("m_signal = %s", cls.m_signal.name());
		calc_parity();
	end
endmodule

/*
    ncsim> run
    m_signal = GREEN
    Called from somewhere
    ncsim: *W,RNQUIE: Simulation is complete.
*/

// 沒有 import 的話
/*
        e_signal 	m_signal;
            |
    ncvlog: *E,NOIPRT (testbench.sv,15|8): Unrecognized declaration 'e_signal' could be an unsupported keyword, a spelling mistake or missing instance port list '()' [SystemVerilog].
            cls.m_signal = GREEN;
                            |
    ncvlog: *E,UNDIDN (testbench.sv,23|19): 'GREEN': undeclared identifier [12.5(IEEE)].
*/