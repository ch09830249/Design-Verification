package my_pkg;
	typedef enum bit { READ, WRITE } e_rd_wr;   // READ: 0, WRITE: 1
endpackage

import my_pkg::*;

module tb;
  typedef enum bit { WRITE, READ } e_wr_rd;     // WRITE: 0, READ: 1

	initial begin
        e_wr_rd  	opc1 = READ;
        e_rd_wr  	opc2 = READ;
      $display ("READ1 = %0d READ2 = %0d ", opc1, opc2);
	end
endmodule

/*
    ncsim> run
    READ1 = 1 READ2 = 1             就近原則, e_wr_rd 的 READ 最近所以皆為 1
    ncsim: *W,RNQUIE: Simulation is complete.
*/

module tb;
	initial begin
        e_wr_rd  	opc1 = READ;
        e_rd_wr  	opc2 = my_pkg::READ;
      $display ("READ1 = %0d READ2 = %0d ", opc1, opc2);
	end
endmodule

/*
    ncsim> run
    READ1 = 1 READ2 = 0         要特別指定用 pkg 中的 READ
    ncsim: *W,RNQUIE: Simulation is complete.
*/