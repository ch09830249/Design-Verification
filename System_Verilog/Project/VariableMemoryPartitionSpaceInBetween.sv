// Variable Memory Partition with space in between
class MemoryBlock;

  bit [31:0] 		m_ram_start; 			// RAM 的 Start address
  bit [31:0] 		m_ram_end; 				// RAM 的 End address

  rand int			    m_num_part; 			      // partitions 數量
  rand bit [31:0] 	m_part_start []; 		    // Partition start array
  rand int 			    m_part_size [];		 	    // 紀錄每個 partition 的大小
  rand int 			    m_space[]; 	 			      // 多一個 array 去紀錄每個 space partition 的 size (space 的 start addr 不用紀錄)

  constraint c_parts { m_num_part > 4; m_num_part < 10; }

  constraint c_size { 
                     m_part_size.size() == m_num_part;
                     m_space.size() == m_num_part - 1;                                  // space 的數量是 partition 數量 - 1
                     m_space.sum() + m_part_size.sum() == m_ram_end - m_ram_start + 1;  // space + mem 總共 size 限制
                     foreach (m_part_size[i]) {
                       m_part_size[i] inside {16, 32, 64, 128, 512, 1024};              // 隨機產生 mem 和 space 的 size
                       if (i < m_space.size())                                          // for 最後一個 mem partition, space partition 不用再產生 size
                       	  m_space[i] inside {0, 16, 32, 64, 128, 512, 1024};
                     }
                    }

  constraint c_part { m_part_start.size() == m_num_part;
                      foreach (m_part_start[i]) {
                        if (i)
                          m_part_start[i] == m_part_start[i-1] + m_part_size[i-1] +  m_space[i-1];  // 需多加一個 space 的 size
                        else
                          m_part_start[i] == m_ram_start;
                      }
                    }

  function void display();
    $display ("------ Memory Block --------");
    $display ("RAM StartAddr   = 0x%0h", m_ram_start);
    $display ("RAM EndAddr     = 0x%0h", m_ram_end);
    $display ("# Partitions = %0d", m_num_part);
    $display ("------ Partitions --------");
    foreach (m_part_start[i])
      $display ("Partition %0d start = 0x%0h, size = %0d bytes, space = %0d bytes", i, m_part_start[i], m_part_size[i], m_space[i]);
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
    ------ Memory Block --------
    RAM StartAddr   = 0x0
    RAM EndAddr     = 0x7ff
    # Partitions = 5
    ------ Partitions --------
    Partition 0 start = 0x0, size = 128 bytes, space = 64 bytes
    Partition 1 start = 0xc0, size = 32 bytes, space = 128 bytes
    Partition 2 start = 0x160, size = 32 bytes, space = 0 bytes
    Partition 3 start = 0x180, size = 1024 bytes, space = 512 bytes
    Partition 4 start = 0x780, size = 128 bytes, space = 0 bytes
*/