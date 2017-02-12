
// =======================================================================
//   Filename:     top_level_tb.sv
//   Created by:   Surendra Maddula
//   Date:         05-May-2016
//
//   Description:  Top level testbench module for instr_decode.sv, memory_pdp.sv and instr_exec.sv modules
// =======================================================================
import pdp8_pkg::*;

`include "pdp8_pkg.sv"


module top_level_tb ();

wire                   clk;
wire 									reset_n;
wire 									stall;
wire [`ADDR_WIDTH-1:0] PC_value;

wire                   ifu_rd_req;
wire [`ADDR_WIDTH-1:0] ifu_rd_addr;
wire [`DATA_WIDTH-1:0] ifu_rd_data;

wire 									exec_rd_req;
wire [`ADDR_WIDTH-1:0] exec_rd_addr;

wire                   exec_wr_req;
wire [`ADDR_WIDTH-1:0] exec_wr_addr;
wire [`DATA_WIDTH-1:0] exec_wr_data;
wire [`DATA_WIDTH-1:0] exec_rd_data;

wire [`ADDR_WIDTH-1:0] base_addr;
pdp_mem_opcode_s pdp_mem_opcode;
pdp_op7_opcode_s pdp_op7_opcode;


memory_pdp MEM(	.clk         		 (clk),
								.ifu_rd_req      (ifu_rd_req),
								.ifu_rd_addr     (ifu_rd_addr),
								.ifu_rd_data     (ifu_rd_data),
								.exec_rd_req     (exec_rd_req),
								.exec_rd_addr    (exec_rd_addr),
								.exec_rd_data    (exec_rd_data),
								.exec_wr_req     (exec_wr_req),
								.exec_wr_addr    (exec_wr_addr),
								.exec_wr_data    (exec_wr_data));
													


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

												

instr_exec EXE(	.clk          		(clk),
								.reset_n      		(reset_n),
								.base_addr        (base_addr),
								.pdp_mem_opcode   (pdp_mem_opcode),
								.pdp_op7_opcode   (pdp_op7_opcode),
								.stall      			(stall),
								.PC_value         (PC_value),
								.exec_wr_req      (exec_wr_req),
								.exec_wr_addr     (exec_wr_addr),
								.exec_wr_data     (exec_wr_data),
								.exec_rd_req			(exec_rd_req),
								.exec_rd_addr 		(exec_rd_addr),
								.exec_rd_data 		(exec_rd_data));							
		
									
chip_sb SB( .clk(clk),
	    .reset_n(reset_n),
	    .ifu_rd_req(ifu_rd_req),
	    .ifu_rd_addr(ifu_rd_addr),
	    .ifu_rd_data(ifu_rd_data),
	    .exec_rd_req(exec_rd_req),
	    .exec_rd_addr(exec_rd_addr),
	    .exec_rd_data(exec_rd_data),
	    .exec_wr_req(exec_wr_req),
	    .exec_wr_addr(exec_wr_addr),
	    .exec_wr_data(exec_wr_data),
	    .pdp_mem_opcode(pdp_mem_opcode),
	    .pdp_op7_opcode(pdp_op7_opcode));



ifd_checker IFD_CHEK(	.clk             (clk),
									.reset_n         (reset_n),
									.stall           (stall),
									.PC_value        (PC_value),
									.ifu_rd_req      (ifu_rd_req),
									.ifu_rd_addr     (ifu_rd_addr),
									.ifu_rd_data     (ifu_rd_data),
									.base_addr       (base_addr),
									.pdp_mem_opcode  (pdp_mem_opcode),
									.pdp_op7_opcode  (pdp_op7_opcode));



exe_checker EXE_CHEK(    						.clk (clk),
								.reset_n(reset_n),
								.base_addr(base_addr),
								.pdp_mem_opcode(pdp_mem_opcode),
								.pdp_op7_opcode(pdp_op7_opcode),
								.stall(stall),
								.PC_value(PC_value),
								.exec_wr_req(exec_wr_req),
								.exec_wr_addr(exec_wr_addr),
								.exec_wr_data(exec_wr_data),
								.exec_rd_req(exec_rd_req),
								.exec_rd_addr(exec_rd_addr),
								.exec_rd_data(exec_rd_data) );



endmodule
