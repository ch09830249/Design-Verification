// Equal partition
class MemoryBlock;

  bit [31:0] 		m_ram_start; 			// RAM 的 Start address
  bit [31:0] 		m_ram_end; 				// RAM 的 End address

  rand int			    m_num_part; 			      // partitions 數量
  rand bit [31:0] 	m_part_start []; 		    // Partition start addr array
  rand int 			    m_part_size; 		 	      // partition 的 size

  constraint c_parts { m_num_part > 4; m_num_part < 10; }                       // 限制 partition 數量, 最多切 9 塊, 最少切 5 塊

  constraint c_size { m_part_size == (m_ram_end - m_ram_start)/m_num_part; }    // 平均切, 每個 partition size 都一樣大

  constraint c_part { 
                      m_part_start.size() == m_num_part;                        // Partition start addr array 的大小要和 partition 數量一致
                      foreach (m_part_start[i]) {                               // 每個 partition 的 start addr =
                        if (i)                                                  //     前一個 partition 的 start addr + 前一個 partition 的 size
                          m_part_start[i] == m_part_start[i-1] + m_part_size;
                        else
                          m_part_start[i] == m_ram_start;
                      }
                    }

  function void display();
    $display ("------ Memory Block --------");
    $display ("RAM StartAddr   = 0x%0h", m_ram_start);
    $display ("RAM EndAddr     = 0x%0h", m_ram_end);
    $display ("# Partitions = %0d", m_num_part);
    $display ("Partition Size = %0d bytes", m_part_size);
    $display ("------ Partitions --------");
    foreach (m_part_start[i])                   // 印出每個 partition 的 start addr
      $display ("Partition %0d start = 0x%0h", i, m_part_start[i]);
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
    # Partitions = 9
    Partition Size = 227 bytes
    ------ Partitions --------
    Partition 0 start = 0x0
    Partition 1 start = 0xe3
    Partition 2 start = 0x1c6
    Partition 3 start = 0x2a9
    Partition 4 start = 0x38c
    Partition 5 start = 0x46f
    Partition 6 start = 0x552
    Partition 7 start = 0x635
    Partition 8 start = 0x718
*/