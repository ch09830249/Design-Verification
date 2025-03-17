// Memory Block Randomization   在 RAM 隨機一個 Memory Block
class MemoryBlock;

  bit [31:0] 		m_ram_start; 			// RAM 的 Start address
  bit [31:0] 		m_ram_end; 				// RAM 的 End address

  rand bit [31:0] 	m_start_addr; 			// 隨機出來的 block 的 start address
  rand bit [31:0]   m_end_addr; 			  // 隨機出來的 block 的 end addr
  rand int 			    m_block_size; 			// Block size in KB

  constraint c_addr { m_start_addr >= m_ram_start; 	// Block start addr >= RAM start addr
                      m_start_addr < m_ram_end; 	  // Block start addr < RAM end addr
                      m_start_addr % 4 == 0;  		  // Block addr should be aligned to 4-byte boundary  (4K-align)
                      m_end_addr == m_start_addr + m_block_size - 1; };

  constraint c_blk_size { m_block_size inside {64, 128, 512}; }; 	// Block's size should be either 64/128/512 bytes

  function void display();
    $display ("------ Memory Block --------");
    $display ("RAM StartAddr   = 0x%0h", m_ram_start);
    $display ("RAM EndAddr     = 0x%0h", m_ram_end);
	  $display ("Block StartAddr = 0x%0h", m_start_addr);
    $display ("Block EndAddr   = 0x%0h", m_end_addr);
    $display ("Block Size      = %0d bytes", m_block_size);
  endfunction
endclass

module tb;
  initial begin
    MemoryBlock mb = new;
    mb.m_ram_start = 32'h0;
    mb.m_ram_end   = 32'h7FF; 		// 2KB RAM
    mb.randomize();
    mb.display();
  end
endmodule

/*
    RAM StartAddr   = 0x0
    RAM EndAddr     = 0x7ff
    Block StartAddr = 0x714
    Block EndAddr   = 0x753
    Block Size      = 64 bytes
*/