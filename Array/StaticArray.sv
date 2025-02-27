/*
  A static array is one whose size is known before compilation time. 
  Static arrays are further categorized into
    -- Packed array
    -- Unpacked array

    EX:
      bit [3:0] 	data; 			// Packed array or vector   PS: 左邊都是 Packed
      logic 		queue [9:0]; 	// Unpacked array
*/

module tb;
  // A one-dimensional packed array is also called as a vector.
	bit [7:0] 	m_data; 	// A vector or 1D packed array

	initial begin
		// 1. Assign a value to the vector
		m_data = 8'hA2;

		// 2. Iterate through each bit of the vector and print value
		for (int i = 0; i < $size(m_data); i++) begin
			$display ("m_data[%0d] = %b", i, m_data[i]);
		end
	end
endmodule

/*
  little-endian
    m_data[0] = 0
    m_data[1] = 1
    m_data[2] = 0
    m_data[3] = 0
    m_data[4] = 0
    m_data[5] = 1
    m_data[6] = 0
    m_data[7] = 1
*/