
//------------------------------------------------------------------------------
//File       : fsm_101.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 03-02-2026
//Module     : fsm_101
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: 101 Sequence Detector used for basic functional coverage example.
//------------------------------------------------------------------------------

module fsm_101(
  input logic clk, rst, in,
  output logic out
);
  typedef enum logic [1:0] {S0, S1, S2} state_t;
  
  state_t state, next;

  // State Register (Sequential)
  always_ff @(posedge clk) begin
    if(rst) 
      state <= S0;
    else    
      state <= next;
  end
  
  // Next State & Output Logic (Combinational)
  // Implements 101 Overlapping Sequence
  always_comb begin
    next = state;
    out = 0;
    
    case(state)
      S0: begin // Idle
        if (in) next = S1;
        else    next = S0;
      end
      
      S1: begin // Seen '1'
        if (in) next = S1; // Stay in S1 if 11
        else    next = S2; // Go to S2 if 10
      end
      
      S2: begin // Seen '10'
        if (in) begin
          next = S1; // 101 detected! Go back to S1 for overlap
          out = 1;
        end else begin
          next = S0; // 100 Reset
        end
      end
    endcase
  end
endmodule
