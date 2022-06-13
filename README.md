# nvm-log

## State

The logger maintains just one piece of state: the position (specifically, the address of the first byte) where the next log can be written.

## Writing a message

Our messages do not cross page boundaries. This is convenient for erasing (erasing a page will never erase half of a message) and works better with the ring-buffer structure of the memory.

The message is first seralized to a temporary buffer, to determine its length. Then either

- The message fits in the remaining space of the current page. The message is written to the page, starting at the current position
- The message does not fit in the current page. In this case the current block is sealed with zero bytes. NOTE: there can be many consequtive zero bytes, even zero words, when the message type is big.
    The message is then written to the next page, which may loop back around to the first page if the last page is full.

A message starts with a header word (which indicates whether the message is active or not). Then come the serialized bytes, and then we pad to the next word boundary with zero bytes.

## Finding the current position 

After a reboot, the current log position is lost. We can find the log position by finding a non-sealed page (so the final word is 0xFFFFFFFF), then searching in that page for the last zero byte. The start of the next word is the current position.

If all blocks are sealed, we default to using the first byte of the first page as the current position. The first page is cleared in this case.

## Iterating over messages

Starting from the current position, we scan through the pages to find the next page that has any content, then parse the messages, starting with either an active or inactive header. For those with an active header, the message bytes are decoded, and the header is set to inactive (this works because the active -> inactive transformation only turns 1 bits into 0 bits). The decoded message is yielded.
