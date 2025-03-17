// Variable Memory Partition
class MemoryBlock;

  bit [31:0] 		m_ram_start; 			// RAM 的 Start address
  bit [31:0] 		m_ram_end; 				// RAM 的 End address

  rand int			    m_num_part; 			      // partitions 數量
  rand bit [31:0] 	m_part_start []; 		    // Partition start array
  rand int 			    m_part_size  [];		 	  // 紀錄每個 partition 的大小

  constraint c_parts { m_num_part > 4; m_num_part < 10; }                       // 限制 partition 數量, 最多切 9 塊, 最少切 5 塊

  constraint c_size { 
                        m_part_size.size() == m_num_part;
                        m_part_size.sum() == m_ram_end - m_ram_start + 1;       // 這邊限制每個 partition 加總起來的 size 為多少
                        foreach (m_part_size[i])
                            m_part_size[i] inside {16, 32, 64, 128, 512, 1024}; // 這邊決定每個 partition 的 size
                    }

  // 限制 start addr 同 Equal Memory
  constraint c_part { 
                        m_part_start.size() == m_num_part;
                        foreach (m_part_start[i]) {
                            if (i)
                              m_part_start[i] == m_part_start[i-1] + m_part_size[i-1];
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
      $display ("Partition %0d start = 0x%0h, size = %0d bytes", i, m_part_start[i], m_part_size[i]);
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
    # Partitions = 7
    ------ Partitions --------
    Partition 0 start = 0x0, size = 512 bytes
    Partition 1 start = 0x200, size = 128 bytes
    Partition 2 start = 0x280, size = 64 bytes
    Partition 3 start = 0x2c0, size = 1024 bytes
    Partition 4 start = 0x6c0, size = 128 bytes
    Partition 5 start = 0x740, size = 128 bytes
    Partition 6 start = 0x7c0, size = 64 bytes
*/