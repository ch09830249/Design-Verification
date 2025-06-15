/*
	1. A packed array is guaranteed to be represented as a contiguous set of bits.
	2. A packed array is used to refer to dimensions declared before the variable name.		維度放變數名稱左邊
	3. A multidimensional packed array is still a set of contiguous bits but are also segmented into smaller groups.
*/

module tb;
  	bit [3:0][7:0] 	m_data; 	// A MDA, 4 bytes
	int md1[2][3];
	int k = 1;

	initial begin
		// 1. Assign a value to the MDA
		m_data = 32'hface_cafe;		// 4*8 = 32 bits

		$display ("m_data = 0x%0h", m_data);	// little-endian

		// 2. Iterate through each segment of the MDA and print value
		for (int i = 0; i < $size(m_data); i++) begin
			$display ("m_data[%0d] = %b (0x%0h)", i, m_data[i], m_data[i]);
		end

		foreach (md1[i, j]) begin
			md1[i][j] = k;
			k++;
		end

		foreach (md1[i, j]) begin
			$display ("m_data[%0d][%0d] = %b (0x%0h)", i, j, md1[i][j], md1[i][j]);
		end
	end
endmodule

/*
	little-endian
		m_data = 0xfacecafe
		m_data[0] = 11111110 (0xfe)
		m_data[1] = 11001010 (0xca)
		m_data[2] = 11001110 (0xce)
		m_data[3] = 11111010 (0xfa)

		m_data[0][0] = 00000000000000000000000000000001 (0x1)
		m_data[0][1] = 00000000000000000000000000000010 (0x2)
		m_data[0][2] = 00000000000000000000000000000011 (0x3)
		m_data[1][0] = 00000000000000000000000000000100 (0x4)
		m_data[1][1] = 00000000000000000000000000000101 (0x5)
		m_data[1][2] = 00000000000000000000000000000110 (0x6)
*/