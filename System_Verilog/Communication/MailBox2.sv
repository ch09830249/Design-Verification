class comp2;
	mailbox #(byte) 	list;

	...
endclass

module tb;
	s_mbox 	m_mbx;
	...

	initial begin
		m_comp1.names = m_mbx;
		m_comp2.list  = m_mbx;
	end
endmodule

/*
 m_comp2.list = m_mbx;
                         |
ncvlog: *E,TYCMPAT (testbench.sv,34|25): assignment operator type check failed (expecting datatype compatible with 'mailbox' but found '$unit::s_mbox (mailbox)' instead).
*/