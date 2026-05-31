# 📘 AHB-Lite UVM VIP Description

## 🧩 Module Overview

This project implements a configurable and reusable AHB-Lite (Advanced High-performance Bus Lite) UVM Verification IP based on the AMBA® AHB Protocol Specification (IHI 0033C).  
It supports three modes of operation — **master VIP**, **slave VIP**, and **loopback testbench** — through flexible configuration.

The VIP includes layered base components, driver/monitor/sequencer agents, protocol timing assertions (SystemVerilog Assertions), optional bus functional models (BFMs), and reference model support.  
It is designed to validate both master and slave DUTs by instantiating the corresponding passive or active agent, and can be used for directed or random stimulus generation.

### Supported Features

- AHB-Lite master transactions: read/write stimulus generation with burst support
- AHB-Lite slave response handling: data return and memory emulation
- Configurable transfer types: IDLE, BUSY, NONSEQ, SEQ
- Burst type support: SINGLE, INCR (undefined-length); fixed-length and wrapping bursts (INCR4/8/16, WRAP4/8/16) not yet implemented
- Loopback test support between master and slave agents
- Built-in SystemVerilog Assertions (SVA) for protocol timing checks
- UVM scoreboard and passive agent monitoring support
- Functional coverage for read/write address, data, burst, and control signals
- Optional BFMs for standalone integration without UVM

---

## 🔧 I/O Signals

| Signal       | Direction | Width        | Description                              |
|--------------|-----------|--------------|------------------------------------------|
| `HCLK`       | Input     | 1            | AHB clock                                |
| `HRESETn`    | Input     | 1            | Active-low reset                         |
| `HADDR`      | Input     | D_ADDR_WIDTH | Address bus                              |
| `HTRANS`     | Input     | 2            | Transfer type (IDLE/BUSY/NONSEQ/SEQ)     |
| `HWRITE`     | Input     | 1            | Write enable (1=write, 0=read)           |
| `HSIZE`      | Input     | 3            | Transfer size (byte/halfword/word/...)   |
| `HBURST`     | Input     | 3            | Burst type                               |
| `HPROT`      | Input     | 4            | Protection control                       |
| `HWDATA`     | Input     | D_DATA_WIDTH | Write data bus                           |
| `HMASTLOCK`  | Input     | 1            | Locked transfer indicator                |
| `HSEL`       | Output    | D_SLV_COUNT  | Slave select                             |
| `HRDATA`     | Output    | D_DATA_WIDTH | Read data bus                            |
| `HREADY`     | Output    | 1            | Transfer done (slave extends when 0)     |
| `HRESP`      | Output    | 1            | Transfer response (OKAY/ERROR)           |

PS: `HPROT` and `HMASTLOCK` are sampled but not used in current implementation.

---

## 🔁 AHB-Lite Protocol Behavior

- **Address Phase**:
  - Master drives `HADDR`, `HTRANS`, `HWRITE`, `HSIZE`, `HBURST`, `HPROT` on the rising edge of `HCLK`.
  - `HTRANS` must be NONSEQ or SEQ to initiate a valid transfer; IDLE indicates no transfer.

- **Data Phase**:
  - Follows the address phase by one clock cycle.
  - For writes, master drives `HWDATA`; for reads, slave returns `HRDATA`.
    - The UVM slave driver provides HRDATA in the same cycle as the address phase (zero wait state); the BFM provides HRDATA one cycle later.
  - Slave may insert wait states by asserting `HREADY` low.
  - Slave signals completion with `HREADY` high and a valid `HRESP`.

- **Burst Transfers**:
  - The master driver supports SINGLE and undefined-length INCR bursts. HBURST is driven correctly for these types.
  - Fixed-length incrementing (INCR4/8/16) and wrapping bursts (WRAP4/8/16) are not yet implemented.
  - The slave driver and BFM sample HBURST but do not use it; burst sequencing is handled entirely by the master side.
  - The master may use BUSY transfers to insert idle cycles within a burst.

- **Error Response**:
  - A two-cycle error response: first cycle `HRESP=ERROR, HREADY=0`; second cycle `HRESP=ERROR, HREADY=1`.
    - Not yet implemented

---

## 📷 AHB-Lite Block Diagram

### Loopback Test
<img width="1024" height="856" alt="image" src="https://github.com/user-attachments/assets/0911c572-b418-4e5e-b085-5a074c2d4c30" />

### Master VIP
<img width="671" height="303" alt="testbench_diagram2" src="https://github.com/user-attachments/assets/1ca266a8-fdd4-4fd0-bbc9-7654db022fcd" />

### Slave VIP
<img width="492" height="352" alt="testbench_diagram1" src="https://github.com/user-attachments/assets/0400d0b2-e05a-4a50-9e8f-36fec99cb057" />

---

## 📁 Directory Structure
```
AHB_VIP/
|
├── bfm/
│   └── ahb_slave_bfm.sv
│
├── seq/
│   └── ahb_master_seq.sv
│
├── test/
│   └── ahb_basic_rw_test.sv
│
├── top/
│   └── sim_top.sv
│
├── vip/
│   ├── base/
│   │   ├── ahb_agent_base.sv
│   │   ├── ahb_driver_base.sv
│   │   └── ahb_monitor_base.sv
│   │
│   ├── common/
│   │   ├── ahb_coverage.sv
│   │   ├── ahb_define.svh
│   │   ├── ahb_env.sv
│   │   ├── ahb_package.svh
│   │   ├── ahb_scoreboard.sv
│   │   └── ahb_seq_item.sv
│   │
│   ├── interface/
│   │   └── ahb_interface.sv
│   │
│   ├── master/
│   │   ├── ahb_master_agent.sv
│   │   ├── ahb_master_driver.sv
│   │   └── ahb_master_monitor.sv
│   │
│   ├── slave/
│   │   ├── ahb_slave_agent.sv
│   │   ├── ahb_slave_driver.sv
│   │   └── ahb_slave_monitor.sv
│   │
│   └── sva/
│       ├── ahb_protocol_sva.sv
│       └── bind_ahb_protocol_sva.sv
│
├── ahb_vip.f
│
└── README.md
```

## Simulation
```
xrun -f ahb_vip.f -access +r +UVM_TESTNAME=ahb_basic_rw_test
```
