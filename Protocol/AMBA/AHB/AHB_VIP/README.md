# 📘 AHB-Lite UVM VIP Description

## 🧩 Module Overview

This project implements a configurable and reusable AHB-Lite (Advanced High-performance Bus Lite) UVM Verification IP based on the AMBA® AHB Protocol Specification (IHI 0033B).  
It supports three modes of operation — **master VIP**, **slave VIP**, and **loopback testbench** — through flexible configuration.

The VIP includes layered base components, driver/monitor/sequencer agents, protocol timing assertions (SystemVerilog Assertions), optional bus functional models (BFMs), and reference model support.  
It is designed to validate both master and slave DUTs by instantiating the corresponding passive or active agent, and can be used for directed or random stimulus generation.

### Supported Features

- AHB-Lite master transactions: read/write stimulus generation with burst support
- AHB-Lite slave response handling: data return and memory emulation
- Configurable transfer types: IDLE, BUSY, NONSEQ, SEQ
- Burst type support: SINGLE, INCR (Currently not support WRAP4/8/16, INCR4/8/16)
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
| `HSEL`       | Input     | 1            | Slave select                             |
| `HADDR`      | Input     | Configurable | Address bus                              |
| `HTRANS`     | Input     | 2            | Transfer type (IDLE/BUSY/NONSEQ/SEQ)     |
| `HWRITE`     | Input     | 1            | Write enable (1=write, 0=read)           |
| `HSIZE`      | Input     | 3            | Transfer size (byte/halfword/word/...)   |
| `HBURST`     | Input     | 3            | Burst type                               |
| `HPROT`      | Input     | 4            | Protection control                       |
| `HWDATA`     | Input     | Configurable | Write data bus                           |
| `HRDATA`     | Output    | Configurable | Read data bus                            |
| `HREADY`     | Output    | 1            | Transfer done (slave extends when 0)     |
| `HRESP`      | Output    | 1            | Transfer response (OKAY/ERROR)           |

---

## 🔁 AHB-Lite Protocol Behavior

- **Address Phase**:
  - Master drives `HADDR`, `HTRANS`, `HWRITE`, `HSIZE`, `HBURST`, `HPROT` on the rising edge of `HCLK`.
  - `HTRANS` must be NONSEQ or SEQ to initiate a valid transfer; IDLE indicates no transfer.

- **Data Phase**:
  - Follows the address phase by one clock cycle.
  - For writes, master drives `HWDATA`; for reads, slave returns `HRDATA`.
  - Slave may insert wait states by asserting `HREADY` low.
  - Slave signals completion with `HREADY` high and a valid `HRESP`.

- **Burst Transfers**:
  - Incrementing bursts (INCR) or wrapping bursts (WRAP) of 4, 8, or 16 beats are supported.
  - Undefined-length incrementing bursts (INCR) are also supported.
  - The master may use BUSY transfers to insert idle cycles within a burst.

- **Error Response**:
  - A two-cycle error response: first cycle `HRESP=ERROR, HREADY=0`; second cycle `HRESP=ERROR, HREADY=1`.

---

## 📷 AHB-Lite Block Diagram

### Loopback Test

### Master VIP Test

### Slave VIP Test

---

## 📁 Directory Structure
```
AHB_VIP/
|
├── bfm/
│   └── ahb_slave_bfm.sv
│
├── seq/
│   ├── ahb_master_seq.sv
│   └── ahb_slave_seq.sv
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


xrun -f ahb_vip.f -access +r +UVM_TESTNAME=ahb_basic_rw_test
