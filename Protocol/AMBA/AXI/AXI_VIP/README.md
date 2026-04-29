# 📘 APB UVM VIP Description

## 🧩 Module Overview

This project implements a configurable and reusable APB (Advanced Peripheral Bus) UVM Verification IP based on the AMBA® APB protocol specification (IHI 0024E).  
It supports three modes of operation — **master VIP**, **slave VIP**, and **loopback testbench** — through flexible configuration.

The VIP includes layered base components, driver/monitor/sequencer agents, protocol timing assertions (SystemVerilog Assertions), optional bus functional models (BFMs), and reference model support.  
It is designed to validate both master and slave DUTs by instantiating the corresponding passive or active agent, and can be used for directed or random stimulus generation.

### Supported Features

- APB master transactions: read/write stimulus generation
- APB slave response handling: data return and memory emulation
- Configurable setup and access phase timing
- Loopback test support between master and slave agents
- Built-in SystemVerilog Assertions (SVA) for protocol timing checks
- UVM scoreboard and passive agent monitoring support
- Functional coverage for read/write address, data, and control signals
- Optional BFMs for standalone integration without UVM

---

## 🔧 I/O Signals

| Signal     | Direction (Master) | Width            | Description                        |
|------------|--------------------|------------------|------------------------------------|
| `PCLK`     | Input              | 1                | APB clock                          |
| `PRESETn`  | Input              | 1                | Active-low reset                   |
| `PADDR`    | Output             | `D_ADDR_WIDTH    | Address bus                        |
| `PWRITE`   | Output             | 1                | Write enable (1=write, 0=read)     |
| `PSEL`     | Output             | `D_SLV_COUNT     | Slave select (one-hot, multi-slave)|
| `PENABLE`  | Output             | 1                | Enable for access phase            |
| `PWDATA`   | Output             | `D_DATA_WIDTH    | Write data bus                     |
| `PREADY`   | Input              | 1                | Slave ready signal                 |
| `PRDATA`   | Input              | `D_DATA_WIDTH    | Read data bus                      |
| `PSLVERR`  | Input              | 1                | Slave error response               |

---

## 🔁 APB Protocol Behavior

- **Setup Phase**:
  - Master asserts `PSEL` with valid `PADDR`, `PWRITE`, `PWDATA` (for write) on the rising edge of `PCLK`.

- **Access Phase**:
  - Master asserts `PENABLE` while keeping `PSEL` high.
  - Slave responds with `PREADY` and provides `PRDATA` for read operations.

- **Timing Control**:
  - Single setup and access phase; no burst support.
  - Ready signal may insert wait states.
 
- **Error Response**:
  - Slave asserts `PSLVERR` high during the access phase to indicate a transfer error.
  - `PSLVERR` is only valid when `PSEL`, `PENABLE`, and `PREADY` are all high.
  - ⚠️ Status: Planned — PSLVERR detection is defined but not yet implemented.

---

## 📷 APB Block Diagram

### Loopback Test
<img width="671" height="561" alt="testbench_diagram" src="https://github.com/user-attachments/assets/8a7cc0c8-c89a-4c20-aadd-8a910702b5e0" />

### Master VIP
<img width="671" height="303" alt="testbench_diagram2" src="https://github.com/user-attachments/assets/7898e680-db44-4497-818b-23fa1b96da0c" />

### Slave VIP
<img width="492" height="352" alt="testbench_diagram1" src="https://github.com/user-attachments/assets/aa01d6cc-7a1c-4520-8128-1d5d7763a6e2" />

---

## 📁 Directory Structure
```
APB_VIP/
|
├── bfm/
│   └── apb_slave_bfm.sv
│
├── seq/
│   ├── apb_master_seq.sv
│   └── apb_slave_seq.sv
│
├── test/
│   └── apb_basic_rw_test.sv
│
├── top/
│   └── sim_top.sv
│
├── vip/
│   ├── base/
│   │   ├── apb_agent_base.sv
│   │   ├── apb_driver_base.sv
│   │   └── apb_monitor_base.sv
│   │
│   ├── common/
│   │   ├── apb_coverage.sv
│   │   ├── apb_define.svh
│   │   ├── apb_env.sv
│   │   ├── apb_package.svh
│   │   ├── apb_scoreboard.sv
│   │   └── apb_seq_item.sv
│   │
│   ├── interface/
│   │   └── apb_interface.sv
│   │
│   ├── master/
│   │   ├── apb_master_agent.sv
│   │   ├── apb_master_driver.sv
│   │   └── apb_master_monitor.sv
│   │
│   ├── slave/
│   │   ├── apb_slave_agent.sv
│   │   ├── apb_slave_driver.sv
│   │   └── apb_slave_monitor.sv
│   │
│   └── sva/
│       ├── apb_protocol_sva.sv
│       └── bind_apb_protocol_sva.sv
│
├── apb_vip.f
│
└── README.md
```

xrun -f apb_vip.f -access +r +UVM_TESTNAME=apb_basic_rw_test
