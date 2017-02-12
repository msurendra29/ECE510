// =======================================================================
//   Department of Electrical and Computer Engineering
//   Portland State University
//
//   Course name:  ECE 510 - Pre-Silicon Validation
//   Term & Year:  Spring 2016
//   Project Team: Surendra Maddula, Bharath Reddy Godi.
//
//   Project:      Hardware implementation of PDP8 
//                 Instruction Set Architecture (ISA) level simulator
//
//   Filename:     top_level_tb.sv
//   Description:  Top level testbench module
//   Created by:   Surendra Maddula
//   Date:         May 23, 2016
//
//   Copyright:    Surendra Maddula, Bharath Reddy Godi
// =======================================================================


`include "pdp8_pkg.sv"
`timescale 1ns/1ps

import pdp8_pkg::*;

module top_level_tb ();

wire                   clk;
wire 									reset_n;
wire 									stall;
wire [`ADDR_WIDTH-1:0] PC_value;

wire                   ifu_rd_req;
wire [`ADDR_WIDTH-1:0] ifu_rd_addr;
wire [`DATA_WIDTH-1:0] ifu_rd_data;


wire [`ADDR_WIDTH-1:0] base_addr;
pdp_mem_opcode_s pdp_mem_opcode;
pdp_op7_opcode_s pdp_op7_opcode;



	memory_pdp_stub MEM(	.clk         		 (clk),
									.ifu_rd_req      (ifu_rd_req),
									.ifu_rd_addr     (ifu_rd_addr),
									.ifu_rd_data     (ifu_rd_data));
													


clkgen_driver #(
   .CLOCK_PERIOD(10)) clkgen_driver (
   .clk     (clk),
   .reset_n (reset_n));

instr_decode DEC(	.clk             (clk),
									.reset_n         (reset_n),
									.stall           (stall),
									.PC_value        (PC_value),
									.ifu_rd_req      (ifu_rd_req),
									.ifu_rd_addr     (ifu_rd_addr),
									.ifu_rd_data     (ifu_rd_data),
									.base_addr       (base_addr),
									.pdp_mem_opcode  (pdp_mem_opcode),
									.pdp_op7_opcode  (pdp_op7_opcode));								

												

instr_exec_stub EXE(	.clk          		(clk),
								.reset_n      		(reset_n),
								.base_addr        (base_addr),
								.pdp_mem_opcode   (pdp_mem_opcode),
								.pdp_op7_opcode   (pdp_op7_opcode),
								.stall      			(stall),
								.PC_value         (PC_value));							
												


ifd_checker CHEK(	.clk             (clk),
									.reset_n         (reset_n),
									.stall           (stall),
									.PC_value        (PC_value),
									.ifu_rd_req      (ifu_rd_req),
									.ifu_rd_addr     (ifu_rd_addr),
									.ifu_rd_data     (ifu_rd_data),
									.base_addr       (base_addr),
									.pdp_mem_opcode  (pdp_mem_opcode),
									.pdp_op7_opcode  (pdp_op7_opcode));

endmodule
