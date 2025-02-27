module tb;
  bit [2:0][3:0][7:0] 	m_data; 	// An MDA, 12 bytes

	initial begin
		// 1. Assign a value to the MDA
      m_data[0] = 32'hface_cafe;
      m_data[1] = 32'h1234_5678;
      m_data[2] = 32'hc0de_fade;

      // m_data gets a packed value
      $display ("m_data = 0x%0h", m_data);

		// 2. Iterate through each segment of the MDA and print value
      foreach (m_data[i]) begin
        $display ("m_data[%0d] = 0x%0h", i, m_data[i]);
        foreach (m_data[i][j]) begin
          $display ("m_data[%0d][%0d] = 0x%0h", i, j, m_data[i][j]);
        end
      end
	end
endmodule

