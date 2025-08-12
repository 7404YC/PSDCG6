class spi_tran extends uvm_sequence_item;
    // transaction input 
    randc   logic       rst_n;
    rand    logic       start;
    rand    logic [7:0] tx_data;

    // transaction output 
            logic       miso;
            logic [7:0] rx_data;
            logic       busy;
            logic       done;
            logic       mosi;
            logic       cs_n;


    int seq_count;
    int seq_index;

    int tran_count;
    int tran_index;
    int tran_ready;
    string tran_type;
    string tran_dir;

    real tran_time;

    `uvm_object_utils(spi_tran)

    function new(string name = "spi_tran");
        super.new(name);
    endfunction
endclass
