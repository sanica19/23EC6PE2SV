// File        :Arbiter.sv
// Author      :Sanica M S /1BM23EC229
// Created     :04-02-2026
// Module      :arbiter
// Project     :SystemVerilog & Verification(23EC6PE2SV)
// Faculty     :Prof.Ajaykumar Devarapalli
// Description :This module implements a priority arbiter that grants access based on incoming request signals.On reset, all grants are cleared, and the highest-priority active request receives the grant.
module arbiter (input clk,rst,input [3:0] req,output reg[3:0] gnt);
  always_ff @(posedge clk) begin
    if(rst) gnt<=0;
    else if (req[0]) gnt<=4'b0001;
    else if (req[1]) gnt<=4'b0010;
    else if (req[2]) gnt<=4'b0100;
    else if (req[3]) gnt<=4'b1000;
    else gnt<=4'b000;
  end
endmodule
