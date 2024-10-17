module ibc::commitment {

    use aptos_std::string::{Self, String};
    use aptos_std::string_utils;
    use aptos_std::hash;
    use ibc::height::{Self, Height};

    // Function to convert a String to vector<u8>
    public inline fun keccak256(s: String): vector<u8> {
        let vec_val = *string::bytes(&s);
        hash::sha2_256(vec_val)
    }

    // Generate the path for client state
    public fun client_state_path(client_id: String): String {
        let path = string::utf8(b"clients/");
        string::append(&mut path, client_id);
        string::append_utf8(&mut path, b"/clientState");
        path
    }

    // Generate the path for consensus state
    public fun consensus_state_path(
        client_id: String, revision_number: u64, revision_height: u64
    ): String {
        let path = string::utf8(b"clients/");
        string::append(&mut path, client_id);
        string::append_utf8(&mut path, b"/consensusStates/");
        string::append(&mut path, string_utils::to_string(&revision_number));
        string::append_utf8(&mut path, b"-");
        string::append(&mut path, string_utils::to_string(&revision_height));
        path
    }

    // Generate the path for connection
    public fun connection_path(connection_id: String): String {
        let path = string::utf8(b"connections/");
        string::append(&mut path, connection_id);
        path
    }

    // Generate the path for channel
    public fun channel_path(port_id: String, channel_id: String): String {
        let path = string::utf8(b"channelEnds/ports/");
        string::append(&mut path, port_id);
        string::append_utf8(&mut path, b"/channels/");
        string::append(&mut path, channel_id);
        path
    }

    // Generate the path for packet commitment
    public fun packet_path(
        port_id: String, channel_id: String, sequence: u64
    ): String {
        let path = string::utf8(b"commitments/ports/");
        string::append(&mut path, port_id);
        string::append_utf8(&mut path, b"/channels/");
        string::append(&mut path, channel_id);
        string::append_utf8(&mut path, b"/sequences/");
        string::append(&mut path, string_utils::to_string(&sequence));
        path
    }

    // Generate the path for packet acknowledgment commitment
    public fun packet_acknowledgement_path(
        port_id: String, channel_id: String, sequence: u64
    ): String {
        let path = string::utf8(b"acks/ports/");
        string::append(&mut path, port_id);
        string::append_utf8(&mut path, b"/channels/");
        string::append(&mut path, channel_id);
        string::append_utf8(&mut path, b"/sequences/");
        string::append(&mut path, string_utils::to_string(&sequence));
        path
    }

    // Generate the path for packet receipt commitment
    public fun packet_receipt_path(
        port_id: String, channel_id: String, sequence: u64
    ): String {
        let path = string::utf8(b"receipts/ports/");
        string::append(&mut path, port_id);
        string::append_utf8(&mut path, b"/channels/");
        string::append(&mut path, channel_id);
        string::append_utf8(&mut path, b"/sequences/");
        string::append(&mut path, string_utils::to_string(&sequence));
        path
    }

    // Generate the path for next sequence send commitment
    public fun next_sequence_send_path(
        port_id: String, channel_id: String
    ): String {
        let path = string::utf8(b"nextSequenceSend/ports/");
        string::append(&mut path, port_id);
        string::append_utf8(&mut path, b"/channels/");
        string::append(&mut path, channel_id);
        path
    }

    // Generate the path for next sequence receive commitment
    public fun next_sequence_recv_path(
        port_id: String, channel_id: String
    ): String {
        let path = string::utf8(b"nextSequenceRecv/ports/");
        string::append(&mut path, port_id);
        string::append_utf8(&mut path, b"/channels/");
        string::append(&mut path, channel_id);
        path
    }

    // Generate the path for next sequence acknowledge commitment
    public fun next_sequence_ack_path(port_id: String, channel_id: String): String {
        let path = string::utf8(b"nextSequenceAck/ports/");
        string::append(&mut path, port_id);
        string::append_utf8(&mut path, b"/channels/");
        string::append(&mut path, channel_id);
        path
    }

    // Key generation functions
    public fun client_state_key(client_id: String): vector<u8> {
        *string::bytes(&client_state_path(client_id))
    }

    public fun consensus_state_key(client_id: String, height: Height): vector<u8> {
        *string::bytes(
            &consensus_state_path(
                client_id,
                height::get_revision_number(&height),
                height::get_revision_height(&height)
            )
        )
    }

    public fun connection_key(connection_id: String): vector<u8> {
        *string::bytes(&connection_path(connection_id))
    }

    public fun channel_key(port_id: String, channel_id: String): vector<u8> {
        *string::bytes(&channel_path(port_id, channel_id))
    }

    public fun packet_key(
        port_id: String, channel_id: String, sequence: u64
    ): vector<u8> {
        *string::bytes(&packet_path(port_id, channel_id, sequence))
    }

    public fun packet_acknowledgement_key(
        port_id: String, channel_id: String, sequence: u64
    ): vector<u8> {
        *string::bytes(&packet_acknowledgement_path(port_id, channel_id, sequence))
    }

    public fun packet_receipt_key(
        port_id: String, channel_id: String, sequence: u64
    ): vector<u8> {
        *string::bytes(&packet_receipt_path(port_id, channel_id, sequence))
    }

    public fun next_sequence_send_key(port_id: String, channel_id: String): vector<u8> {
        *string::bytes(&next_sequence_send_path(port_id, channel_id))
    }

    public fun next_sequence_recv_key(port_id: String, channel_id: String): vector<u8> {
        *string::bytes(&next_sequence_recv_path(port_id, channel_id))
    }

    public fun next_sequence_ack_key(port_id: String, channel_id: String): vector<u8> {
        *string::bytes(&next_sequence_ack_path(port_id, channel_id))
    }
}
