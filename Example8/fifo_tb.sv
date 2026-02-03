//------------------------------------------------------------------------------
//File       : fifo_tb.sv
//Author     : Krishna Gupta/1BM23EC229
//Created    :03-02-2026
//Module     : tb
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: FIFO with Interfaces used for basic sequential coverage example.
//------------------------------------------------------------------------------

`timescale 1ns/1ps

module tb;
  bit clk = 0;
  always #5 clk = ~clk;
  
  fifo_if vif(clk);
  
  fifo dut(
    .clk(clk), 
    .wr(vif.wr), 
    .rd(vif.rd), 
    .din(vif.din), 
    .full(vif.full), 
    .empty(vif.empty)
  );
  
  covergroup cg_fifo @(posedge clk);
    cross_wr_full: cross vif.wr, vif.full;
  endgroup

  cg_fifo cg; 
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    
    // 1. Instantiate
    cg = new(); 
    
    // 2. Initialize
    vif.wr = 0; vif.rd = 0;
    @(posedge clk);         

    // 3. Fill the FIFO
    vif.wr = 1; 
    repeat(18) @(posedge clk); 
    
    // 4. Stop Writing
    vif.wr = 0;
    
    // Wait for the covergroup to see this new state
    repeat(5) @(posedge clk); 
    
    $display("Coverage: %0.2f %%", cg.get_inst_coverage());
    $finish;
  end
endmodule
