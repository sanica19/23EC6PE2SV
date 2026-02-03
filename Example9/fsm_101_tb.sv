
//------------------------------------------------------------------------------
//File       : fsm_101.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 03-02-2026
//Module     : tb
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: 101 Sequence Detector used for basic functional coverage example.
//------------------------------------------------------------------------------

`timescale 1ns/1ps

module tb;
  logic clk = 0, rst, in, out;
  
  always #5 clk = ~clk;

  fsm_101 dut(.*);
  
  covergroup cg_fsm @(posedge clk);
    cp_state: coverpoint dut.state;
  endgroup
  
  //Declare handle
  cg_fsm cg;

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    
    // Instantiate Covergroup
    cg = new();
    
    // Reset
    rst = 1; in = 0;
    #15;
    rst = 0;
    
    // Stimulus: Drive sequence 1-0-1-1-0-1
    $display("Starting Stimulus...");
    
    @(posedge clk) in = 1; // S0 -> S1
    @(posedge clk) in = 0; // S1 -> S2
    @(posedge clk) in = 1; // S2 -> S1 (Output should occur)
    
    @(posedge clk) in = 1; 
    @(posedge clk) in = 0;
    @(posedge clk) in = 1; // Another detection
    
    #10;
    $display("Coverage = %0.2f %%", cg.get_inst_coverage());
    $finish;
  end
endmodule
