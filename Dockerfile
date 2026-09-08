FROM node:22-alpine
WORKDIR /app
COPY . .
ENV PORT=7788
EXPOSE 7788
CMD ["node", "server.mjs"]
