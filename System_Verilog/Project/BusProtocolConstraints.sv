// Burst [ 0 -> 1 byte, 1 -> 2 bytes, 2 -> 3 bytes, 3 -> 4 bytes]
// Length -> max 8 transactions per burst
// Protocol expects to send only first addr, and slave should calculate all
// other addresses from burst and length properties

class BusTransaction;
  rand int 			m_addr;
  rand bit [31:0]	m_data;
  rand bit [1:0] 	m_burst; 	  // Size of a single transaction in bytes (4 bytes max)
  rand bit [2:0] 	m_length; 	// Total number of transactions

  constraint c_addr { m_addr % 4 == 0; } // Always aligned to 4-byte boundary

  function void display(int idx = 0);
    $display ("------ Transaction %0d------", idx);
    $display (" Addr 	= 0x%0h", m_addr);
    $display (" Data 	= 0x%0h", m_data);
    $display (" Burst 	= %0d bytes/xfr", m_burst + 1);
    $display (" Length  = %0d", m_length + 1);
  endfunction
endclass

module tb;
  int 				slave_start;
  int  				slave_end;
  BusTransaction	bt;

  // Assume we are targeting a slave with addr range 0x200 to 0x800
  initial begin
  	slave_start = 32'h200;
    slave_end 	= 32'h800;
    bt = new;

    bt.randomize() with { m_addr >= slave_start;
                          m_addr < slave_end;
                         (m_burst + 1) * (m_length + 1) + m_addr < slave_end;
                        };
    bt.display();
  end
endmodule

/*
    ------ Transaction 0------
    Addr 	= 0x6e0
    Data 	= 0xbbe5ea58
    Burst 	= 4 bytes/xfr
    Length  = 5
*/